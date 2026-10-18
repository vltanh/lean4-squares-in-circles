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

def tilt_053_000 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11145551/50000000), (11145551/50000000), (1053419/6250000), (9640773/50000000), (9640773/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11145551/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (9640773/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(497853/12500000), (1/100000000), (5414293/100000000), (51769/800000), (1/100000000), (3445097/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1845496201573990694714044529553756770653/24037213313514684831044850000000000000000), (11740935188869/16919665625000), (-7203655939247128875380779708800756770653/12018606656757342415522425000000000000000), (11740935188869/16919665625000), (-12561815676920267056047514888047756770653/24037213313514684831044850000000000000000)]
    bernstein := [(3419969261987186050876094988886331740002808067/61535266082597593167474816000000000000000000000), (361449073501878822503929701379870090781959883/6153526608259759316747481600000000000000000000), (114214654324068726244890655932995180511808553/1846057982477927795024244480000000000000000000), (3998016232607120022621113210763498797913931/61535266082597593167474816000000000000000000), (418711518188702477052035867524854293281283/6153526608259759316747481600000000000000000)]
    reserve := (55577386427/1000000000000) }

theorem tilt_053_000_valid : tilt_053_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_053_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_053_000]
  · intro i; fin_cases i <;> norm_num [tilt_053_000]
  · norm_num [tilt_053_000]
  · norm_num [tilt_053_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_053_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_053_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_053_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_053_000]

def tilt_053_001 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11145551/50000000), (11145551/50000000), (1053419/6250000), (9640773/50000000), (9640773/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11145551/100000000), 0], ![(22291/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (9640773/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(497853/12500000), (1/100000000), (5414293/100000000), (51769/800000), (1/100000000), (3445097/100000000), (1/100000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-1839691555711173424736565923869608319153/24037213313514684831044850000000000000000), (11740935188869/16919665625000), (-7197851293384311605403301103116608319153/12018606656757342415522425000000000000000), (11740935188869/16919665625000), (-12556011031057449786070036282363608319153/24037213313514684831044850000000000000000)]
    bernstein := [(3436371803885146442504924911162976752461899567/61535266082597593167474816000000000000000000000), (363098109540400717914561620990074140220143383/6153526608259759316747481600000000000000000000), (114712106669866303464690594961521018656907053/1846057982477927795024244480000000000000000000), (4014692980170994039266409244894057299073431/61535266082597593167474816000000000000000000), (420389060843056668075527184567573195764783/6153526608259759316747481600000000000000000)]
    reserve := (27921970787/500000000000) }

theorem tilt_053_001_valid : tilt_053_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_053_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_053_001]
  · intro i; fin_cases i <;> norm_num [tilt_053_001]
  · norm_num [tilt_053_001]
  · norm_num [tilt_053_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_053_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_053_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_053_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_053_001]

def tilt_053_002 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11145551/50000000), (11145551/50000000), (1053419/6250000), (9640773/50000000), (9640773/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11145551/100000000), 0], ![0, 0, (6603/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (9640773/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(497853/12500000), (1159/20000000), (5414293/100000000), (51769/800000), (1/100000000), (3445097/100000000), (1/100000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-7031104530241463814918241658214559248881/91341410591355802357970430000000000000000), (11740935188869/16919665625000), (-27392111533399388901451835339353159248881/45670705295677901178985215000000000000000), (11740935188869/16919665625000), (-47753118536557313987985429020491759248881/91341410591355802357970430000000000000000)]
    bernstein := [(12944400756884159736268217590140171941122776559/233834011113870854036404300800000000000000000000), (1368330671969395393186973656957299809944645591/23383401111387085403640430080000000000000000000), (432454339413317780731841928803316298530147181/7015020333416125621092129024000000000000000000), (15140118599587216556171231663801050877964887/233834011113870854036404300800000000000000000), (1585838488445842951221328159726374377073391/23383401111387085403640430080000000000000000)]
    reserve := (55357219829/1000000000000) }

theorem tilt_053_002_valid : tilt_053_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_053_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_053_002]
  · intro i; fin_cases i <;> norm_num [tilt_053_002]
  · norm_num [tilt_053_002]
  · norm_num [tilt_053_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_053_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_053_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_053_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_053_002]

def tilt_053_003 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11145551/50000000), (11145551/50000000), (1053419/6250000), (9640773/50000000), (9640773/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11156697/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (9640773/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3978841/100000000), (1/100000000), (5414293/100000000), (51769/800000), (1/100000000), (3445097/100000000), (1/100000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-7344643887545487968551457470077138365099/96052700152010816554122725000000000000000), (11740935188869/16919665625000), (-28755849252184374137663839305006638365099/48026350076005408277061362500000000000000), (11740935188869/16919665625000), (-50167054616823260306776221139936138365099/96052700152010816554122725000000000000000)]
    bernstein := [(13750852431745435584910668938926328277299484661/245894912389147690378554176000000000000000000000), (1452861344737273581368829502258044091997390189/24589491238914769037855417600000000000000000000), (458969161214887069789367775397988246249380799/7376847371674430711356625280000000000000000000), (16062143238838531526447463813618018477070573/245894912389147690378554176000000000000000000), (1681829190306760299449850455004872012486389/24589491238914769037855417600000000000000000)]
    reserve := (55921663031/1000000000000) }

theorem tilt_053_003_valid : tilt_053_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_053_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_053_003]
  · intro i; fin_cases i <;> norm_num [tilt_053_003]
  · norm_num [tilt_053_003]
  · norm_num [tilt_053_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_053_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_053_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_053_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_053_003]

def tilt_053_004 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11145551/50000000), (11145551/50000000), (1053419/6250000), (9640773/50000000), (9640773/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (2226881/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (9640773/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3986807/100000000), (1/100000000), (5414293/100000000), (51769/800000), (1/100000000), (3445097/100000000), (1/100000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-3698965816177746967232178206775935297217/48122503178053331047118037500000000000000), (11740935188869/16919665625000), (-14426002084550856605342928006299185297217/24061251589026665523559018750000000000000), (11740935188869/16919665625000), (-25153038352923966243453677805822435297217/48122503178053331047118037500000000000000)]
    bernstein := [(6834678128454253227368523593778879972100792863/123193608135816527480622176000000000000000000000), (722404534838117245290847064622906382848919687/12319360813581652748062217600000000000000000000), (228290762863591960216798227579334985463800317/3695808244074495824418665280000000000000000000), (7991725925159754887232304026043687391095559/123193608135816527480622176000000000000000000), (837022923995271116586868612576732199104287/12319360813581652748062217600000000000000000)]
    reserve := (1386979047/25000000000) }

theorem tilt_053_004_valid : tilt_053_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_053_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_053_004]
  · intro i; fin_cases i <;> norm_num [tilt_053_004]
  · norm_num [tilt_053_004]
  · norm_num [tilt_053_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_053_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_053_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_053_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_053_004]

def tilt_053_005 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11145551/50000000), (11145551/50000000), (1053419/6250000), (9640773/50000000), (9640773/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11145551/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (9640773/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(497853/12500000), (1/100000000), (5414293/100000000), (6467919/100000000), (1/100000000), (3445097/100000000), (1/100000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-15321251521500899009652629929683052311463/200210870981391163048319490000000000000000), (11740935188869/16919665625000), (-59950460987051204183739836731462852311463/100105435490695581524159745000000000000000), (11740935188869/16919665625000), (-104579670452601509357827043533242652311463/200210870981391163048319490000000000000000)]
    bernstein := [(28627658739728697073564732906854487225708001657/512539829712361377403697894400000000000000000000), (3024862836104493943155932514722757725088787793/51253982971236137740369789440000000000000000000), (955624829873062808491071991423164918759932363/15376194891370841322110936832000000000000000000), (33444704734972049169482206213908733509166801/512539829712361377403697894400000000000000000), (3502060309005624303087763642601423881987193/51253982971236137740369789440000000000000000)]
    reserve := (1745453297/31250000000) }

theorem tilt_053_005_valid : tilt_053_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_053_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_053_005]
  · intro i; fin_cases i <;> norm_num [tilt_053_005]
  · norm_num [tilt_053_005]
  · norm_num [tilt_053_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_053_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_053_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_053_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_053_005]

def tilt_053_006 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11145551/50000000), (11145551/50000000), (1053419/6250000), (9640773/50000000), (9640773/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11145551/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (9640773/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(497853/12500000), (1/100000000), (5414293/100000000), (1618583/25000000), (1/100000000), (3445097/100000000), (1/100000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-7220302202077500726027111404305535575591/93941897749204492838105493750000000000000), (11740935188869/16919665625000), (-28160986450088378413151901883721660575591/46970948874602246419052746875000000000000), (11740935188869/16919665625000), (-49101670698099256100276692363137785575591/93941897749204492838105493750000000000000)]
    bernstein := [(13343947688588664268191357878768651734132400249/240491258237963501665550064000000000000000000000), (1410405636249051497344967196831998639615928401/24049125823796350166555006400000000000000000000), (445707075545696615355508188504122615957426891/7214737747138905049966501920000000000000000000), (15602696124533689546090485573916658041327057/240491258237963501665550064000000000000000000), (1634159804869813263961153431266103968654201/24049125823796350166555006400000000000000000)]
    reserve := (55486206801/1000000000000) }

theorem tilt_053_006_valid : tilt_053_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_053_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_053_006]
  · intro i; fin_cases i <;> norm_num [tilt_053_006]
  · norm_num [tilt_053_006]
  · norm_num [tilt_053_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_053_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_053_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_053_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_053_006]

def tilt_053_007 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11145551/50000000), (11145551/50000000), (1053419/6250000), (9640773/50000000), (9640773/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11145551/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (9640773/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(497853/12500000), (1/100000000), (541029/10000000), (51769/800000), (1/100000000), (3445097/100000000), (1/100000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-30640645724099827338472754523048066737/400324027587644296908675000000000000000), (11740935188869/16907156250000), (-120016282719601677607358426961334866737/200162013793822148454337500000000000000), (11740935188869/16907156250000), (-209391919715103527876244099399621666737/400324027587644296908675000000000000000)]
    bernstein := [(57311993248895091364577653787217809939588143/1024829510624369400086208000000000000000000000), (263281043933396138316314385543711789841409/4455780480975519130809600000000000000000000), (1912990722420257382409484777363463403105837/30744885318731082002586240000000000000000000), (66948040643108696648474120928304154664599/1024829510624369400086208000000000000000000), (7010037586629295089490323290942157513007/102482951062436940008620800000000000000000)]
    reserve := (27961720781/500000000000) }

theorem tilt_053_007_valid : tilt_053_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_053_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_053_007]
  · intro i; fin_cases i <;> norm_num [tilt_053_007]
  · norm_num [tilt_053_007]
  · norm_num [tilt_053_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_053_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_053_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_053_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_053_007]

def tilt_053_008 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11145551/50000000), (11145551/50000000), (1053419/6250000), (9640773/50000000), (9640773/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11145551/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (9640773/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(497853/12500000), (1/100000000), (5418297/100000000), (51769/800000), (1/100000000), (3445097/100000000), (1/100000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-8215603653120292754866307147113304549/106911064050469276434714000000000000000), (11740935188869/16932178125000), (-32010191409780551804179679938116824549/53455532025234638217357000000000000000), (11740935188869/16932178125000), (-55804779166440810853493052729120344549/106911064050469276434714000000000000000)]
    bernstein := [(15167301123489166275433445323343574450873211/273692323969201347672867840000000000000000000), (1603194682622148299901903434600621624619139/27369232396920134767286784000000000000000000), (506650326257926983144533272321510093615249/8210769719076040430186035200000000000000000), (17736732359207221202320201847146902590723/273692323969201347672867840000000000000000), (1857729456186108746020599149191415305339/27369232396920134767286784000000000000000)]
    reserve := (13854335503/250000000000) }

theorem tilt_053_008_valid : tilt_053_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_053_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_053_008]
  · intro i; fin_cases i <;> norm_num [tilt_053_008]
  · norm_num [tilt_053_008]
  · norm_num [tilt_053_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_053_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_053_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_053_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_053_008]

def tilt_053_009 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11145551/50000000), (11145551/50000000), (1053419/6250000), (9640773/50000000), (9640773/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11145551/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (9640773/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(497853/12500000), (1/100000000), (5414293/100000000), (80849/1250000), (1/100000000), (3445097/100000000), (1/100000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-11490945507628785647532579060237206825417/150158176451880372725387400000000000000000), (11740935188869/16919665625000), (-44962857781857420449728864289385206825417/75079088225940186362693700000000000000000), (11740935188869/16919665625000), (-78434770056086055251925149518533206825417/150158176451880372725387400000000000000000)]
    bernstein := [(21470732991536844525920703631346631587802832663/384404931716813754176991744000000000000000000000), (2268646031848161426622029371589266782174109887/38440493171681375417699174400000000000000000000), (716718297016954453101664090863782900268588517/11532147951504412625309752320000000000000000000), (25083517806097514375424381682206032790576959/384404931716813754176991744000000000000000000), (2626544166861872333426992786314207227454487/38440493171681375417699174400000000000000000)]
    reserve := (6981808511/125000000000) }

theorem tilt_053_009_valid : tilt_053_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_053_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_053_009]
  · intro i; fin_cases i <;> norm_num [tilt_053_009]
  · norm_num [tilt_053_009]
  · norm_num [tilt_053_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_053_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_053_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_053_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_053_009]

def tilt_053_010 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11145551/50000000), (11145551/50000000), (1053419/6250000), (9640773/50000000), (9640773/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11145551/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (9640773/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(497853/12500000), (1/100000000), (5414293/100000000), (6474333/100000000), (1/100000000), (3445097/100000000), (1/100000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-76992284551477351891817759137320150850543/1002047064097094593200777150000000000000000), (11740935188869/16919665625000), (-300359617697366086698688058436513150850543/501023532048547296600388575000000000000000), (11740935188869/16919665625000), (-523726950843254821505558357735706150850543/1002047064097094593200777150000000000000000)]
    bernstein := [(142404085246402379585664623464561261706418761777/2565240484088562158593989504000000000000000000000), (15051227974881136863566128276652763327020089673/256524048408856215859398950400000000000000000000), (4756290668910046752826963292413940450259315443/76957214522656864757819685120000000000000000000), (166498552777576735573281077614677604606389961/2565240484088562158593989504000000000000000000), (17438058735018984342989065401911386404193073/256524048408856215859398950400000000000000000)]
    reserve := (55512957217/1000000000000) }

theorem tilt_053_010_valid : tilt_053_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_053_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_053_010]
  · intro i; fin_cases i <;> norm_num [tilt_053_010]
  · norm_num [tilt_053_010]
  · norm_num [tilt_053_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_053_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_053_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_053_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_053_010]

def tilt_053_011 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11145551/50000000), (11145551/50000000), (1053419/6250000), (9640773/50000000), (9640773/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11145551/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(9641/50000000), 0, 0, 0, 0], ![0, 0, 0, (9640773/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(497853/12500000), (1/100000000), (5414293/100000000), (51769/800000), (1/100000000), (3445097/100000000), (1/100000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-1840475120533088449711810902501107527153/24037213313514684831044850000000000000000), (11740935188869/16919665625000), (-7198634858206226630378546081748107527153/12018606656757342415522425000000000000000), (11740935188869/16919665625000), (-12556794595879364811045281260995107527153/24037213313514684831044850000000000000000)]
    bernstein := [(3434157636970407019615851685100252918964611567/61535266082597593167474816000000000000000000000), (362875507393707700384369250255630161718631383/6153526608259759316747481600000000000000000000), (114644955948193007739337075537780168030515053/1846057982477927795024244480000000000000000000), (4012441798437632172512530421285760074489431/61535266082597593167474816000000000000000000), (420162610609523225857681385743069924652783/6153526608259759316747481600000000000000000)]
    reserve := (55807959493/1000000000000) }

theorem tilt_053_011_valid : tilt_053_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_053_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_053_011]
  · intro i; fin_cases i <;> norm_num [tilt_053_011]
  · norm_num [tilt_053_011]
  · norm_num [tilt_053_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_053_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_053_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_053_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_053_011]

def tilt_053_012 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11145551/50000000), (11145551/50000000), (1053419/6250000), (9640773/50000000), (9640773/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11145551/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5711/100000000), 0, 0], ![0, 0, 0, (9640773/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(497853/12500000), (1/100000000), (5414293/100000000), (51769/800000), (5013/100000000), (3445097/100000000), (1/100000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-1030251279598278960301486970876975715153533/13388727815627679450891981450000000000000000), (11740935188869/16919665625000), (-4014746253482216926932858465717554715153533/6694363907813839725445990725000000000000000), (11740935188869/16919665625000), (-6999241227366154893564229960558133715153533/13388727815627679450891981450000000000000000)]
    bernstein := [(1898395666813098563551115007916521785654037436387/34275143208006859394283472512000000000000000000000), (200670918088538100037734046969631731043747963563/3427514320800685939428347251200000000000000000000), (63419606739343383599815451928485036361057375433/1028254296240205781828504175360000000000000000000), (2220258712303306322767579603973941964363899691/34275143208006859394283472512000000000000000000), (232554755883174664291058133683754748320628963/3427514320800685939428347251200000000000000000)]
    reserve := (55386950691/1000000000000) }

theorem tilt_053_012_valid : tilt_053_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_053_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_053_012]
  · intro i; fin_cases i <;> norm_num [tilt_053_012]
  · norm_num [tilt_053_012]
  · norm_num [tilt_053_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_053_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_053_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_053_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_053_012]

def tilt_053_013 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11145551/50000000), (11145551/50000000), (1053419/6250000), (9640773/50000000), (9640773/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11145551/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4825207/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(497853/12500000), (1/100000000), (5414293/100000000), (51769/800000), (1/100000000), (860413/25000000), (1/100000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-459293073592393592789675884463041364297/6003294194247973429930650000000000000000), (11740935188869/16919665625000), (-1797493505792287482988415605226041364297/3001647097123986714965325000000000000000), (11740935188869/16919665625000), (-3135693937992181373187155325989041364297/6003294194247973429930650000000000000000)]
    bernstein := [(858713994250720000042106035437468325382744983/15368433137274811980622464000000000000000000000), (90732023667614483676551706200119083858229567/1536843313727481198062246400000000000000000000), (28663910170791658117723383290172296121111397/461052994118244359418673920000000000000000000), (1003157738259910419132794123813100160374719/15368433137274811980622464000000000000000000), (105041273564123140782508886262991045718167/1536843313727481198062246400000000000000000)]
    reserve := (13968795429/250000000000) }

theorem tilt_053_013_valid : tilt_053_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_053_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_053_013]
  · intro i; fin_cases i <;> norm_num [tilt_053_013]
  · norm_num [tilt_053_013]
  · norm_num [tilt_053_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_053_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_053_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_053_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_053_013]

def tilt_053_014 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11145551/50000000), (11145551/50000000), (1053419/6250000), (9640773/50000000), (9640773/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11145551/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (2407783/25000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(497853/12500000), (1/100000000), (5414293/100000000), (51769/800000), (1/100000000), (1724271/50000000), (1/100000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-77049737389611893050155325749550490857/1002552077084894830931962500000000000000), (11740935188869/16919665625000), (-300529643495724426405926637226300490857/501276038542447415465981250000000000000), (11740935188869/16919665625000), (-524009549601836959761697948703050490857/1002552077084894830931962500000000000000)]
    bernstein := [(142423153331412586480020158885908781905432823/2566533317337330767185824000000000000000000000), (15053515205391237820057092050934885102925727/256653331733733076718582400000000000000000000), (4757089449913130505726232425729407984045957/76995999520119923015574720000000000000000000), (166528883008601770108528521156591939767839/2566533317337330767185824000000000000000000), (17441457292646830377417136093402408142327/256653331733733076718582400000000000000000)]
    reserve := (1734138229/31250000000) }

theorem tilt_053_014_valid : tilt_053_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_053_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_053_014]
  · intro i; fin_cases i <;> norm_num [tilt_053_014]
  · norm_num [tilt_053_014]
  · norm_num [tilt_053_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_053_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_053_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_053_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_053_014]

def tilt_053_015 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11145551/50000000), (11145551/50000000), (1053419/6250000), (9640773/50000000), (9640773/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11145551/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(9641/50000000), 0, 0, 0, 0], ![0, 0, 0, (9640773/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(497853/12500000), (1/100000000), (5414293/100000000), (51769/800000), (1/100000000), (3445097/100000000), (1/100000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-1840475120533088449711810902501107527153/24037213313514684831044850000000000000000), (11740935188869/16919665625000), (-7198634858206226630378546081748107527153/12018606656757342415522425000000000000000), (11740935188869/16919665625000), (-12556794595879364811045281260995107527153/24037213313514684831044850000000000000000)]
    bernstein := [(3434157636970407019615851685100252918964611567/61535266082597593167474816000000000000000000000), (362875507393707700384369250255630161718631383/6153526608259759316747481600000000000000000000), (114644955948193007739337075537780168030515053/1846057982477927795024244480000000000000000000), (4012441798437632172512530421285760074489431/61535266082597593167474816000000000000000000), (420162610609523225857681385743069924652783/6153526608259759316747481600000000000000000)]
    reserve := (55807959493/1000000000000) }

theorem tilt_053_015_valid : tilt_053_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_053_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_053_015]
  · intro i; fin_cases i <;> norm_num [tilt_053_015]
  · norm_num [tilt_053_015]
  · norm_num [tilt_053_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_053_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_053_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_053_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_053_015]

def tilt_053_016 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11145551/50000000), (11145551/50000000), (1053419/6250000), (9640773/50000000), (9640773/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11145551/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5711/100000000), 0, 0], ![0, 0, 0, (9640773/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(497853/12500000), (1/100000000), (5414293/100000000), (51769/800000), (5013/100000000), (3445097/100000000), (1/100000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-1030251279598278960301486970876975715153533/13388727815627679450891981450000000000000000), (11740935188869/16919665625000), (-4014746253482216926932858465717554715153533/6694363907813839725445990725000000000000000), (11740935188869/16919665625000), (-6999241227366154893564229960558133715153533/13388727815627679450891981450000000000000000)]
    bernstein := [(1898395666813098563551115007916521785654037436387/34275143208006859394283472512000000000000000000000), (200670918088538100037734046969631731043747963563/3427514320800685939428347251200000000000000000000), (63419606739343383599815451928485036361057375433/1028254296240205781828504175360000000000000000000), (2220258712303306322767579603973941964363899691/34275143208006859394283472512000000000000000000), (232554755883174664291058133683754748320628963/3427514320800685939428347251200000000000000000)]
    reserve := (55386950691/1000000000000) }

theorem tilt_053_016_valid : tilt_053_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_053_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_053_016]
  · intro i; fin_cases i <;> norm_num [tilt_053_016]
  · norm_num [tilt_053_016]
  · norm_num [tilt_053_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_053_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_053_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_053_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_053_016]

def tilt_053_017 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11145551/50000000), (11145551/50000000), (1053419/6250000), (9640773/50000000), (9640773/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11145551/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (9640773/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(497853/12500000), (1/100000000), (5414293/100000000), (51769/800000), (1/100000000), (3445097/100000000), (1/100000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-1845496201573990694714044529553756770653/24037213313514684831044850000000000000000), (11740935188869/16919665625000), (-7203655939247128875380779708800756770653/12018606656757342415522425000000000000000), (11740935188869/16919665625000), (-12561815676920267056047514888047756770653/24037213313514684831044850000000000000000)]
    bernstein := [(3419969261987186050876094988886331740002808067/61535266082597593167474816000000000000000000000), (361449073501878822503929701379870090781959883/6153526608259759316747481600000000000000000000), (114214654324068726244890655932995180511808553/1846057982477927795024244480000000000000000000), (3998016232607120022621113210763498797913931/61535266082597593167474816000000000000000000), (418711518188702477052035867524854293281283/6153526608259759316747481600000000000000000)]
    reserve := (55577386427/1000000000000) }

theorem tilt_053_017_valid : tilt_053_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_053_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_053_017]
  · intro i; fin_cases i <;> norm_num [tilt_053_017]
  · norm_num [tilt_053_017]
  · norm_num [tilt_053_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_053_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_053_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_053_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_053_017]

def tilt_053_018 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11145551/50000000), (11145551/50000000), (1053419/6250000), (9640773/50000000), (9640773/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11145551/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (9640773/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(497853/12500000), (1/100000000), (5414293/100000000), (51769/800000), (1/100000000), (3445097/100000000), (1/100000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-1845496201573990694714044529553756770653/24037213313514684831044850000000000000000), (11740935188869/16919665625000), (-7203655939247128875380779708800756770653/12018606656757342415522425000000000000000), (11740935188869/16919665625000), (-12561815676920267056047514888047756770653/24037213313514684831044850000000000000000)]
    bernstein := [(3419969261987186050876094988886331740002808067/61535266082597593167474816000000000000000000000), (361449073501878822503929701379870090781959883/6153526608259759316747481600000000000000000000), (114214654324068726244890655932995180511808553/1846057982477927795024244480000000000000000000), (3998016232607120022621113210763498797913931/61535266082597593167474816000000000000000000), (418711518188702477052035867524854293281283/6153526608259759316747481600000000000000000)]
    reserve := (55577386427/1000000000000) }

theorem tilt_053_018_valid : tilt_053_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_053_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_053_018]
  · intro i; fin_cases i <;> norm_num [tilt_053_018]
  · norm_num [tilt_053_018]
  · norm_num [tilt_053_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_053_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_053_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_053_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_053_018]

def tilt_053_019 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11145551/50000000), (11145551/50000000), (1053419/6250000), (9640773/50000000), (9640773/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11145551/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (9640773/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(497853/12500000), (1/100000000), (5414293/100000000), (51769/800000), (1/100000000), (3445097/100000000), (1/100000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-1845496201573990694714044529553756770653/24037213313514684831044850000000000000000), (11740935188869/16919665625000), (-7203655939247128875380779708800756770653/12018606656757342415522425000000000000000), (11740935188869/16919665625000), (-12561815676920267056047514888047756770653/24037213313514684831044850000000000000000)]
    bernstein := [(3419969261987186050876094988886331740002808067/61535266082597593167474816000000000000000000000), (361449073501878822503929701379870090781959883/6153526608259759316747481600000000000000000000), (114214654324068726244890655932995180511808553/1846057982477927795024244480000000000000000000), (3998016232607120022621113210763498797913931/61535266082597593167474816000000000000000000), (418711518188702477052035867524854293281283/6153526608259759316747481600000000000000000)]
    reserve := (55577386427/1000000000000) }

theorem tilt_053_019_valid : tilt_053_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_053_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_053_019]
  · intro i; fin_cases i <;> norm_num [tilt_053_019]
  · norm_num [tilt_053_019]
  · norm_num [tilt_053_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_053_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_053_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_053_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_053_019]

def tilt_053_020 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11145551/50000000), (11145551/50000000), (1053419/6250000), (9640773/50000000), (9640773/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11145551/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (9640773/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(497853/12500000), (1/100000000), (5414293/100000000), (51769/800000), (1/100000000), (3445097/100000000), (1/100000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-1845496201573990694714044529553756770653/24037213313514684831044850000000000000000), (11740935188869/16919665625000), (-7203655939247128875380779708800756770653/12018606656757342415522425000000000000000), (11740935188869/16919665625000), (-12561815676920267056047514888047756770653/24037213313514684831044850000000000000000)]
    bernstein := [(3419969261987186050876094988886331740002808067/61535266082597593167474816000000000000000000000), (361449073501878822503929701379870090781959883/6153526608259759316747481600000000000000000000), (114214654324068726244890655932995180511808553/1846057982477927795024244480000000000000000000), (3998016232607120022621113210763498797913931/61535266082597593167474816000000000000000000), (418711518188702477052035867524854293281283/6153526608259759316747481600000000000000000)]
    reserve := (55577386427/1000000000000) }

theorem tilt_053_020_valid : tilt_053_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_053_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_053_020]
  · intro i; fin_cases i <;> norm_num [tilt_053_020]
  · norm_num [tilt_053_020]
  · norm_num [tilt_053_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_053_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_053_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_053_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_053_020]

def tiltBundle053_row : Alternative → Row
  | .zero => tilt_053_000
  | (.spike 0 false false) => tilt_053_001
  | (.spike 0 false true) => tilt_053_002
  | (.spike 0 true false) => tilt_053_003
  | (.spike 0 true true) => tilt_053_004
  | (.spike 1 false false) => tilt_053_005
  | (.spike 1 false true) => tilt_053_006
  | (.spike 1 true false) => tilt_053_007
  | (.spike 1 true true) => tilt_053_008
  | (.spike 2 false false) => tilt_053_009
  | (.spike 2 false true) => tilt_053_010
  | (.spike 2 true false) => tilt_053_011
  | (.spike 2 true true) => tilt_053_012
  | (.spike 3 false false) => tilt_053_013
  | (.spike 3 false true) => tilt_053_014
  | (.spike 3 true false) => tilt_053_015
  | (.spike 3 true true) => tilt_053_016
  | (.spike 4 false false) => tilt_053_017
  | (.spike 4 false true) => tilt_053_018
  | (.spike 4 true false) => tilt_053_019
  | (.spike 4 true true) => tilt_053_020

def tiltBundle053 : TiltBundle where
  interval := ⟨(9/40), (1/4)⟩
  lambda := ![(11145551/50000000), (11145551/50000000), (1053419/6250000), (9640773/50000000), (9640773/50000000), 0, 0]
  row := tiltBundle053_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_053_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_053_001_valid | exact tilt_053_002_valid | exact tilt_053_003_valid | exact tilt_053_004_valid | exact tilt_053_005_valid | exact tilt_053_006_valid | exact tilt_053_007_valid | exact tilt_053_008_valid | exact tilt_053_009_valid | exact tilt_053_010_valid | exact tilt_053_011_valid | exact tilt_053_012_valid | exact tilt_053_013_valid | exact tilt_053_014_valid | exact tilt_053_015_valid | exact tilt_053_016_valid | exact tilt_053_017_valid | exact tilt_053_018_valid | exact tilt_053_019_valid | exact tilt_053_020_valid
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
