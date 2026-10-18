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

def tilt_012_000 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(972291/5000000), (972291/5000000), (100247/1562500), (2259461/25000000), (2259461/25000000), (400831/4000000), (26596089/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(132463/4000000), 0, (16368341/100000000), 0, 0]] i.1) i.2
    mu := ![(2081267/25000000), (1/100000000), (5398897/100000000), (2800617/100000000), (1/100000000), (3409791/100000000), (167473/100000000)]
    alternative := .zero
    polynomial := [(-438602457119754846392508403489670728851102029/2950813954313840649919735874100000000000000000), (-13993661192777047341/2583341363660000000), (-62843893950590449278406274558993185402851102029/1475406977156920324959867937050000000000000000), (-13993661192777047341/2583341363660000000), (-125249185444061143710420040714496700076851102029/2950813954313840649919735874100000000000000000)]
    bernstein := [(143361131206659180526296369783790910110642128060451/7554083723043432063794523837696000000000000000000000), (8560469472273297494734768315433315136225108979747/343367441956519639263387447168000000000000000000000), (149710944394008336115829575652335552257362814536017/5665562792282574047845892878272000000000000000000000), (2016248056728470543791460007464016878512690305083/85841860489129909815846861792000000000000000000000), (7616668374018867522163133708892240522165942634771/472130232690214503987157739856000000000000000000000)]
    reserve := (2016569753/125000000000) }

theorem tilt_012_000_valid : tilt_012_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_012_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_012_000]
  · intro i; fin_cases i <;> norm_num [tilt_012_000]
  · norm_num [tilt_012_000]
  · norm_num [tilt_012_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_012_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_012_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_012_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_012_000]

def tilt_012_001 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(972291/5000000), (972291/5000000), (100247/1562500), (2259461/25000000), (2259461/25000000), (400831/4000000), (26596089/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(9723/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1642593/50000000), 0, (4092913/25000000), 0, 0]] i.1) i.2
    mu := ![(2081267/25000000), (1/100000000), (5398897/100000000), (2800617/100000000), (1/100000000), (3409791/100000000), (167473/100000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-438756940875146743284053777736704221911341279/2950813954313840649919735874100000000000000000), (-69968376261223966005813/12916706818300000000000), (-62844108918291724187439719545241215084902341279/1475406977156920324959867937050000000000000000), (-69968376261223966005813/12916706818300000000000), (-125249460895708301631595385312745725947893341279/2950813954313840649919735874100000000000000000)]
    bernstein := [(142962540157536764474197493781550495131562616281201/7554083723043432063794523837696000000000000000000000), (8542387060766197063758544355163592137264918392497/343367441956519639263387447168000000000000000000000), (149413080977409031859717200306149993662934923176267/5665562792282574047845892878272000000000000000000000), (2011741182975176073035895651906415334321975739833/85841860489129909815846861792000000000000000000000), (7591907519811411979113780069336944724978648995521/472130232690214503987157739856000000000000000000000)]
    reserve := (8040056529/500000000000) }

theorem tilt_012_001_valid : tilt_012_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_012_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_012_001]
  · intro i; fin_cases i <;> norm_num [tilt_012_001]
  · norm_num [tilt_012_001]
  · norm_num [tilt_012_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_012_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_012_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_012_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_012_001]

def tilt_012_002 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(972291/5000000), (972291/5000000), (100247/1562500), (2259461/25000000), (2259461/25000000), (400831/4000000), (26596089/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (9/156250), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(834491/25000000), 0, (16365029/100000000), 0, 0]] i.1) i.2
    mu := ![(2081267/25000000), (1011/20000000), (5398897/100000000), (2800617/100000000), (1/100000000), (3409791/100000000), (167473/100000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-147720840103083617941438389329912916218966976107/994424302603764299022950989571700000000000000000), (-17492092880692244312331/3229176704575000000000), (-21178324574934535157594384505337600868065508976107/497212151301882149511475494785850000000000000000), (-17492092880692244312331/3229176704575000000000), (-42208928309765986697247330621345288819912050976107/994424302603764299022950989571700000000000000000)]
    bernstein := [(48541390065353868072657801758070544043873064605133733/2545726214665636605498754533303552000000000000000000000), (2895254601328938749396650370337339102260870479400101/115714827939347118431761569695616000000000000000000000), (50623520087140393292655838034997061423041311851821511/1909294660999227454124065899977664000000000000000000000), (682061666443790322611285280551050761898143156419789/28928706984836779607940392423904000000000000000000000), (2581021988398376444092243623436708029379970111018293/159107888416602287843672158331472000000000000000000000)]
    reserve := (16221835473/1000000000000) }

theorem tilt_012_002_valid : tilt_012_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_012_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_012_002]
  · intro i; fin_cases i <;> norm_num [tilt_012_002]
  · norm_num [tilt_012_002]
  · norm_num [tilt_012_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_012_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_012_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_012_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_012_002]

def tilt_012_003 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(972291/5000000), (972291/5000000), (100247/1562500), (2259461/25000000), (2259461/25000000), (400831/4000000), (26596089/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1642593/50000000), 0, (4092913/25000000), 0, 0]] i.1) i.2
    mu := ![(4160551/50000000), (1/100000000), (5398897/100000000), (2800617/100000000), (1/100000000), (3409791/100000000), (167473/100000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-876506470809394737443842877635730013894016903/5898816417323872443979656147300000000000000000), (-69968376261223966005813/12916706818300000000000), (-125627751541716932646736259162839243150617016903/2949408208661936221989828073650000000000000000), (-69968376261223966005813/12916706818300000000000), (-250378996612624470556028675448042756287340016903/5898816417323872443979656147300000000000000000)]
    bernstein := [(287314676297445279268986486368938220563731340144457/15100970028349113456587919737088000000000000000000000), (17145860684058718003709351038566891542099199624329/686407728561323338935814533504000000000000000000000), (299824132215087192221022358545611203268658865619219/11325727521261835092440939802816000000000000000000000), (4038818234320325641803963219372191936645700198481/171601932140330834733953633376000000000000000000000), (15271352853947898045856035075226382995920401980697/943810626771819591036744983568000000000000000000000)]
    reserve := (505641453/31250000000) }

theorem tilt_012_003_valid : tilt_012_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_012_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_012_003]
  · intro i; fin_cases i <;> norm_num [tilt_012_003]
  · norm_num [tilt_012_003]
  · norm_num [tilt_012_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_012_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_012_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_012_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_012_003]

def tilt_012_004 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(972291/5000000), (972291/5000000), (100247/1562500), (2259461/25000000), (2259461/25000000), (400831/4000000), (26596089/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(834491/25000000), 0, (16365029/100000000), 0, 0]] i.1) i.2
    mu := ![(1665807/20000000), (1/100000000), (5398897/100000000), (2800617/100000000), (1/100000000), (3409791/100000000), (167473/100000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-2125474030310627927438214828723287216095661/14313794203224128587759124340000000000000000), (-17492092880692244312331/3229176704575000000000), (-304841058355567068785927852398670841124495661/7156897101612064293879562170000000000000000), (-17492092880692244312331/3229176704575000000000), (-607556642680823509644417489968618395032895661/14313794203224128587759124340000000000000000)]
    bernstein := [(700848995957430141568294914406429836727584254659/36643313160253769184663358310400000000000000000000), (41771613279849863895917114605926772523570345923/1665605143647898599302879923200000000000000000000), (730278191354732426358856208843140844260746914353/27482484870190326888497518732800000000000000000000), (9841847641379593286957757324471358918321315547/416401285911974649825719980800000000000000000000), (37284390934652155243815478805871819507168815539/2290207072515860574041459894400000000000000000000)]
    reserve := (8139960657/500000000000) }

theorem tilt_012_004_valid : tilt_012_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_012_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_012_004]
  · intro i; fin_cases i <;> norm_num [tilt_012_004]
  · norm_num [tilt_012_004]
  · norm_num [tilt_012_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_012_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_012_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_012_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_012_004]

def tilt_012_005 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(972291/5000000), (972291/5000000), (100247/1562500), (2259461/25000000), (2259461/25000000), (400831/4000000), (26596089/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1642593/50000000), 0, (4092913/25000000), 0, 0]] i.1) i.2
    mu := ![(2081267/25000000), (1/100000000), (5398897/100000000), (559859/20000000), (1/100000000), (3409791/100000000), (167473/100000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-7636266251453030768792178949334388421192185647/51319926366008900389034618580900000000000000000), (-69968376261223966005813/12916706818300000000000), (-1092976825809232150128474912661530590690251185647/25659963183004450194517309290450000000000000000), (-69968376261223966005813/12916706818300000000000), (-2178317385367011269488157646373726792959310185647/51319926366008900389034618580900000000000000000)]
    bernstein := [(2472137205630691387294909094432026696862757392008993/131379011496982784995928623567104000000000000000000000), (147921452662929397942560039058507986421523169460321/5971773249862853863451301071232000000000000000000000), (2587920408127784636710486759965172127020549185171931/98534258622737088746946467675328000000000000000000000), (34826795121973749837414113159420020901209430555369/1492943312465713465862825267808000000000000000000000), (131152558077138216841672496091548295156228017776753/8211188218561424062245538972944000000000000000000000)]
    reserve := (7986210679/500000000000) }

theorem tilt_012_005_valid : tilt_012_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_012_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_012_005]
  · intro i; fin_cases i <;> norm_num [tilt_012_005]
  · norm_num [tilt_012_005]
  · norm_num [tilt_012_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_012_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_012_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_012_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_012_005]

def tilt_012_006 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(972291/5000000), (972291/5000000), (100247/1562500), (2259461/25000000), (2259461/25000000), (400831/4000000), (26596089/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(834491/25000000), 0, (16365029/100000000), 0, 0]] i.1) i.2
    mu := ![(2081267/25000000), (1/100000000), (5398897/100000000), (2801939/100000000), (1/100000000), (3409791/100000000), (167473/100000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-1089116364204327093399766259269503389465763037/7338342749158964889738884262540000000000000000), (-17492092880692244312331/3229176704575000000000), (-156284215703434442150120511648454978222706163037/3669171374579482444869442131270000000000000000), (-17492092880692244312331/3229176704575000000000), (-311479315042664557206841257037640453055946563037/7338342749158964889738884262540000000000000000)]
    bernstein := [(360768143641290979306104196647179648829980754208403/18786157437846950117731543712102400000000000000000000), (21481531945920018812330403476807376894214021363091/853916247174861368987797441459200000000000000000000), (375487069405283079292240183739196594100439238810401/14089618078385212588298657784076800000000000000000000), (5062184555345789805080417467024596880092016217899/213479061793715342246949360364800000000000000000000), (19205474782755086792009371658369826649792061087363/1174134839865434382358221482006400000000000000000000)]
    reserve := (16357128781/1000000000000) }

theorem tilt_012_006_valid : tilt_012_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_012_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_012_006]
  · intro i; fin_cases i <;> norm_num [tilt_012_006]
  · norm_num [tilt_012_006]
  · norm_num [tilt_012_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_012_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_012_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_012_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_012_006]

def tilt_012_007 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(972291/5000000), (972291/5000000), (100247/1562500), (2259461/25000000), (2259461/25000000), (400831/4000000), (26596089/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1642593/50000000), 0, (4092913/25000000), 0, 0]] i.1) i.2
    mu := ![(2081267/25000000), (1/100000000), (5397439/100000000), (2800617/100000000), (1/100000000), (3409791/100000000), (167473/100000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-614467476325943478232387984602534236390672407/4130023900485754491913252093380000000000000000), (-489640724037303153100317/90392530164700000000000), (-87958843525453590789309464166923015371150472407/2065011950242877245956626046690000000000000000), (-489640724037303153100317/90392530164700000000000), (-175303219574581238100386540349243496505910272407/4130023900485754491913252093380000000000000000)]
    bernstein := [(199062586165494359561281764859630342625715844693433/10572861185243531499297925359052800000000000000000000), (11909630196212034152782962329394464993216722891001/480584599329251431786269334502400000000000000000000), (208360745885977587076204009561700412595606719581411/7929645888932648624473444019289600000000000000000000), (2804229206323719190295521589123662192463354829889/120146149832312857946567333625600000000000000000000), (10563267588732407688744378529041195266443562681993/660803824077720718706120334940800000000000000000000)]
    reserve := (15985481929/1000000000000) }

theorem tilt_012_007_valid : tilt_012_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_012_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_012_007]
  · intro i; fin_cases i <;> norm_num [tilt_012_007]
  · norm_num [tilt_012_007]
  · norm_num [tilt_012_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_012_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_012_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_012_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_012_007]

def tilt_012_008 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(972291/5000000), (972291/5000000), (100247/1562500), (2259461/25000000), (2259461/25000000), (400831/4000000), (26596089/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(834491/25000000), 0, (16365029/100000000), 0, 0]] i.1) i.2
    mu := ![(2081267/25000000), (1/100000000), (1350089/25000000), (2800617/100000000), (1/100000000), (3409791/100000000), (167473/100000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-766694393982589988601547539439332731719156459/5165319920968918589198201781900000000000000000), (-30619787814376124818629/5652586377425000000000), (-110004977096840931747591165012365535077593156459/2582659960484459294599100890950000000000000000), (-30619787814376124818629/5652586377425000000000), (-5347396580480470085526360548421749693255296499/125983412706558989980443945900000000000000000)]
    bernstein := [(253794491229697631116883694580803325835654279267621/13223218997680431588347396561664000000000000000000000), (889033819828217367185820994073131135612003752661/35356200528557303712158814336000000000000000000000), (264179334660275497386054399630285171876136669902407/9917414248260323691260547421248000000000000000000000), (3561293305838185923531330760781508490777588975693/150263852246368540776674960928000000000000000000000), (13507589146647082307136947657682823440443614236341/826451187355026974271712285104000000000000000000000)]
    reserve := (16344085837/1000000000000) }

theorem tilt_012_008_valid : tilt_012_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_012_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_012_008]
  · intro i; fin_cases i <;> norm_num [tilt_012_008]
  · norm_num [tilt_012_008]
  · norm_num [tilt_012_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_012_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_012_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_012_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_012_008]

def tilt_012_009 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(972291/5000000), (972291/5000000), (100247/1562500), (2259461/25000000), (2259461/25000000), (400831/4000000), (26596089/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1642593/50000000), 0, (4092913/25000000), 0, 0]] i.1) i.2
    mu := ![(2081267/25000000), (1/100000000), (5398897/100000000), (43739/1562500), (1/100000000), (3409791/100000000), (167473/100000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-1193167318207786906997792833550312976032281513/8018741359245321747497084737800000000000000000), (-69968376261223966005813/12916706818300000000000), (-170777690330243677735485548107066500769910281513/4009370679622660873748542368900000000000000000), (-69968376261223966005813/12916706818300000000000), (-340362213342279568563973303380582688563788281513/8018741359245321747497084737800000000000000000)]
    bernstein := [(386270825127133275931308475140263864728887008343047/20527977879668023673592536928768000000000000000000000), (23112701151534597944592233133874638685121908327559/933089903621273803345115314944000000000000000000000), (404362146773437865997326367261940342439866145046749/15395983409751017755194402696576000000000000000000000), (5441680187318238801308631511214805641865425269951/233272475905318450836278828736000000000000000000000), (20492547858942887106641963824338287705686104428087/1282998617479251479599533558048000000000000000000000)]
    reserve := (15972384989/1000000000000) }

theorem tilt_012_009_valid : tilt_012_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_012_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_012_009]
  · intro i; fin_cases i <;> norm_num [tilt_012_009]
  · norm_num [tilt_012_009]
  · norm_num [tilt_012_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_012_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_012_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_012_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_012_009]

def tilt_012_010 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(972291/5000000), (972291/5000000), (100247/1562500), (2259461/25000000), (2259461/25000000), (400831/4000000), (26596089/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(834491/25000000), 0, (16365029/100000000), 0, 0]] i.1) i.2
    mu := ![(2081267/25000000), (1/100000000), (5398897/100000000), (2801939/100000000), (1/100000000), (3409791/100000000), (167473/100000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-1088924215522881660120426338941057148515027837/7338342749158964889738884262540000000000000000), (-17492092880692244312331/3229176704575000000000), (-156284023554752996716841171728126531981755427837/3669171374579482444869442131270000000000000000), (-17492092880692244312331/3229176704575000000000), (-311479122893983111773561917117312006814995827837/7338342749158964889738884262540000000000000000)]
    bernstein := [(361265593711860114059755008927007881548761049519603/18786157437846950117731543712102400000000000000000000), (21504101153596555069021832498825687017564525749491/853916247174861368987797441459200000000000000000000), (375858843862158102627805603768523249140427373620801/14089618078385212588298657784076800000000000000000000), (5067809323697741973466534954799203691442887727499/213479061793715342246949360364800000000000000000000), (19236372482880193908760510187104310640911231982563/1174134839865434382358221482006400000000000000000000)]
    reserve := (2047930509/125000000000) }

theorem tilt_012_010_valid : tilt_012_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_012_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_012_010]
  · intro i; fin_cases i <;> norm_num [tilt_012_010]
  · norm_num [tilt_012_010]
  · norm_num [tilt_012_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_012_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_012_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_012_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_012_010]

def tilt_012_011 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(972291/5000000), (972291/5000000), (100247/1562500), (2259461/25000000), (2259461/25000000), (400831/4000000), (26596089/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(4519/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1642593/50000000), 0, (4092913/25000000), 0, 0]] i.1) i.2
    mu := ![(2081267/25000000), (1/100000000), (5398897/100000000), (2800617/100000000), (1/100000000), (3409791/100000000), (167473/100000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-146363218308351244625944677839971122896495093/983604651437946883306578624700000000000000000), (-69968376261223966005813/12916706818300000000000), (-20948147210780543726011166600341474743893495093/491802325718973441653289312350000000000000000), (-69968376261223966005813/12916706818300000000000), (-41749931203252736207396388522842978364890495093/983604651437946883306578624700000000000000000)]
    bernstein := [(47367061025099834919593690469753405337138133139067/2518027907681144021264841279232000000000000000000000), (2834435822202090556528298950545065128048152861499/114455813985506546421129149056000000000000000000000), (49589778950123212990041709783296929943206300696089/1888520930760858015948630959424000000000000000000000), (667333881530749579128055408121511326895122142611/28613953496376636605282287264000000000000000000000), (2512802255957439328214440386380376904635438550507/157376744230071501329052579952000000000000000000000)]
    reserve := (15966795273/1000000000000) }

theorem tilt_012_011_valid : tilt_012_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_012_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_012_011]
  · intro i; fin_cases i <;> norm_num [tilt_012_011]
  · norm_num [tilt_012_011]
  · norm_num [tilt_012_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_012_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_012_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_012_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_012_011]

def tilt_012_012 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(972291/5000000), (972291/5000000), (100247/1562500), (2259461/25000000), (2259461/25000000), (400831/4000000), (26596089/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2677/100000000), 0, 0], ![0, 0, 0, 0, 0], ![(834491/25000000), 0, (16365029/100000000), 0, 0]] i.1) i.2
    mu := ![(2081267/25000000), (1/100000000), (5398897/100000000), (2800617/100000000), (47/2000000), (3409791/100000000), (167473/100000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-20589097670735900764470860728255939789664657467/138688255852750510546227586082700000000000000000), (-17492092880692244312331/3229176704575000000000), (-2953640657127941308371855037144758413786066657467/69344127926375255273113793041350000000000000000), (-17492092880692244312331/3229176704575000000000), (-5886692216585146715979239213561260887782468657467/138688255852750510546227586082700000000000000000)]
    bernstein := [(6803312187617122821485758552223033603690441668175573/355041934983041306998342620371712000000000000000000000), (405306597956299325603025118846177580486864279898581/16138269771956423045379210016896000000000000000000000), (7085248808618499437045401658069470394360294679096791/266281451237280980248756965278784000000000000000000000), (95502493684915283505376033415303350037651769968509/4034567442989105761344802504224000000000000000000000), (362041815528926061399601447791128017289806130648933/22190120936440081687396413773232000000000000000000000)]
    reserve := (1631545031/100000000000) }

theorem tilt_012_012_valid : tilt_012_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_012_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_012_012]
  · intro i; fin_cases i <;> norm_num [tilt_012_012]
  · norm_num [tilt_012_012]
  · norm_num [tilt_012_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_012_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_012_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_012_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_012_012]

def tilt_012_013 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(972291/5000000), (972291/5000000), (100247/1562500), (2259461/25000000), (2259461/25000000), (400831/4000000), (26596089/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1642593/50000000), 0, (4092913/25000000), 0, 0]] i.1) i.2
    mu := ![(2081267/25000000), (1/100000000), (5398897/100000000), (2800617/100000000), (1/100000000), (106503/3125000), (167473/100000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-115976584553001122405291521395820109568736219/779580030601414366499974275662500000000000000), (-69968376261223966005813/12916706818300000000000), (-16602941522862415867932545572805131594856611219/389790015300707183249987137831250000000000000), (-69968376261223966005813/12916706818300000000000), (-33089906461171830613459799624214443080144486219/779580030601414366499974275662500000000000000)]
    bernstein := [(37612293159804922977346453343515330145716877869061/1995724878339620778239934145696000000000000000000000), (24746636228760171825619659893327799334981793299087/997862439169810389119967072848000000000000000000000), (39356185795761228027825286511823355822501256100887/1496793658754715583679950609272000000000000000000000), (5826782462400921037018751908823715217840137148343/249465609792452597279991768212000000000000000000000), (1995953699659683047437195936953430655120728998581/124732804896226298639995884106000000000000000000000)]
    reserve := (16001834491/1000000000000) }

theorem tilt_012_013_valid : tilt_012_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_012_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_012_013]
  · intro i; fin_cases i <;> norm_num [tilt_012_013]
  · norm_num [tilt_012_013]
  · norm_num [tilt_012_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_012_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_012_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_012_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_012_013]

def tilt_012_014 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(972291/5000000), (972291/5000000), (100247/1562500), (2259461/25000000), (2259461/25000000), (400831/4000000), (26596089/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(834491/25000000), 0, (16365029/100000000), 0, 0]] i.1) i.2
    mu := ![(2081267/25000000), (1/100000000), (5398897/100000000), (2800617/100000000), (1/100000000), (106609/3125000), (167473/100000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-833893370085261644450605450767256632696034543/5618562687184215714364942343310000000000000000), (-17492092880692244312331/3229176704575000000000), (-119658187108774621560398977562651564335926634543/2809281343592107857182471171655000000000000000), (-17492092880692244312331/3229176704575000000000), (-238482480847463981476347349674535872039157234543/5618562687184215714364942343310000000000000000)]
    bernstein := [(276175456735894851551426322112499183330486503083617/14383520479191592228774252398873600000000000000000000), (180897089265941678749272130827778620191490379111339/7191760239595796114387126199436800000000000000000000), (15129274979597535236637822085344951175443594782681/567770545231247061662141542060800000000000000000000), (42628614463589439389448329311301299276770279450371/1797940059898949028596781549859200000000000000000000), (14701790052926738684666997384329015032413744251057/898970029949474514298390774929600000000000000000000)]
    reserve := (2044254753/125000000000) }

theorem tilt_012_014_valid : tilt_012_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_012_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_012_014]
  · intro i; fin_cases i <;> norm_num [tilt_012_014]
  · norm_num [tilt_012_014]
  · norm_num [tilt_012_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_012_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_012_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_012_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_012_014]

def tilt_012_015 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(972291/5000000), (972291/5000000), (100247/1562500), (2259461/25000000), (2259461/25000000), (400831/4000000), (26596089/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(4519/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1642593/50000000), 0, (4092913/25000000), 0, 0]] i.1) i.2
    mu := ![(2081267/25000000), (1/100000000), (5398897/100000000), (2800617/100000000), (1/100000000), (3409791/100000000), (167473/100000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-146363218308351244625944677839971122896495093/983604651437946883306578624700000000000000000), (-69968376261223966005813/12916706818300000000000), (-20948147210780543726011166600341474743893495093/491802325718973441653289312350000000000000000), (-69968376261223966005813/12916706818300000000000), (-41749931203252736207396388522842978364890495093/983604651437946883306578624700000000000000000)]
    bernstein := [(47367061025099834919593690469753405337138133139067/2518027907681144021264841279232000000000000000000000), (2834435822202090556528298950545065128048152861499/114455813985506546421129149056000000000000000000000), (49589778950123212990041709783296929943206300696089/1888520930760858015948630959424000000000000000000000), (667333881530749579128055408121511326895122142611/28613953496376636605282287264000000000000000000000), (2512802255957439328214440386380376904635438550507/157376744230071501329052579952000000000000000000000)]
    reserve := (15966795273/1000000000000) }

theorem tilt_012_015_valid : tilt_012_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_012_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_012_015]
  · intro i; fin_cases i <;> norm_num [tilt_012_015]
  · norm_num [tilt_012_015]
  · norm_num [tilt_012_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_012_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_012_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_012_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_012_015]

def tilt_012_016 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(972291/5000000), (972291/5000000), (100247/1562500), (2259461/25000000), (2259461/25000000), (400831/4000000), (26596089/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2677/100000000), 0, 0], ![0, 0, 0, 0, 0], ![(834491/25000000), 0, (16365029/100000000), 0, 0]] i.1) i.2
    mu := ![(2081267/25000000), (1/100000000), (5398897/100000000), (2800617/100000000), (47/2000000), (3409791/100000000), (167473/100000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-20589097670735900764470860728255939789664657467/138688255852750510546227586082700000000000000000), (-17492092880692244312331/3229176704575000000000), (-2953640657127941308371855037144758413786066657467/69344127926375255273113793041350000000000000000), (-17492092880692244312331/3229176704575000000000), (-5886692216585146715979239213561260887782468657467/138688255852750510546227586082700000000000000000)]
    bernstein := [(6803312187617122821485758552223033603690441668175573/355041934983041306998342620371712000000000000000000000), (405306597956299325603025118846177580486864279898581/16138269771956423045379210016896000000000000000000000), (7085248808618499437045401658069470394360294679096791/266281451237280980248756965278784000000000000000000000), (95502493684915283505376033415303350037651769968509/4034567442989105761344802504224000000000000000000000), (362041815528926061399601447791128017289806130648933/22190120936440081687396413773232000000000000000000000)]
    reserve := (1631545031/100000000000) }

theorem tilt_012_016_valid : tilt_012_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_012_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_012_016]
  · intro i; fin_cases i <;> norm_num [tilt_012_016]
  · norm_num [tilt_012_016]
  · norm_num [tilt_012_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_012_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_012_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_012_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_012_016]

def tilt_012_017 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(972291/5000000), (972291/5000000), (100247/1562500), (2259461/25000000), (2259461/25000000), (400831/4000000), (26596089/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1642593/50000000), 0, (4092913/25000000), 0, 0]] i.1) i.2
    mu := ![(2081267/25000000), (1/100000000), (5398897/100000000), (2800617/100000000), (1/100000000), (106503/3125000), (167473/100000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-14845004194023675073524274027074566054658478407/99786243916981038911996707284800000000000000000), (-69968376261223966005813/12916706818300000000000), (-2125176516297628762501012792607466436171506478407/49893121958490519455998353642400000000000000000), (-69968376261223966005813/12916706818300000000000), (-4235508028401233849928501311187858306288354478407/99786243916981038911996707284800000000000000000)]
    bernstein := [(4814369974479060836117640418432849234795146227207433/255452784427471459614711570649088000000000000000000000), (3167567665602803950235492597819978353313430167239011/127726392213735729807355785324544000000000000000000000), (1679196376248722785522649124799241275640585869073137/63863196106867864903677892662272000000000000000000000), (745827713644075061525862412583681685492449929510779/31931598053433932451838946331136000000000000000000000), (255481853059751540512524379394488315861896477675993/15965799026716966225919473165568000000000000000000000)]
    reserve := (16001820681/1000000000000) }

theorem tilt_012_017_valid : tilt_012_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_012_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_012_017]
  · intro i; fin_cases i <;> norm_num [tilt_012_017]
  · norm_num [tilt_012_017]
  · norm_num [tilt_012_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_012_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_012_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_012_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_012_017]

def tilt_012_018 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(972291/5000000), (972291/5000000), (100247/1562500), (2259461/25000000), (2259461/25000000), (400831/4000000), (26596089/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(834491/25000000), 0, (16365029/100000000), 0, 0]] i.1) i.2
    mu := ![(2081267/25000000), (1/100000000), (5398897/100000000), (2800617/100000000), (1/100000000), (106609/3125000), (167473/100000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-26682823059938512618716273480603893246706341651/179794005989894902859678154985920000000000000000), (-17492092880692244312331/3229176704575000000000), (-3829060222697998029929064181060901739750085541651/89897002994947451429839077492960000000000000000), (-17492092880692244312331/3229176704575000000000), (-7631437622336057547239412088641199586253464741651/179794005989894902859678154985920000000000000000)]
    bernstein := [(8842183428182430805892529982469841906492970937817469/460272655334130951320776076763955200000000000000000000), (5790987003523768170981214589795630598180939166883423/230136327667065475660388038381977600000000000000000000), (484316512472960941329508185156127606297077283453717/18168657447399905973188529345945600000000000000000000), (1364683928187545351234756151215832139674145562153047/57534081916766368915097009595494400000000000000000000), (470741060531047916364806251186362124486574989777549/28767040958383184457548504797747200000000000000000000)]
    reserve := (3272780549/200000000000) }

theorem tilt_012_018_valid : tilt_012_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_012_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_012_018]
  · intro i; fin_cases i <;> norm_num [tilt_012_018]
  · norm_num [tilt_012_018]
  · norm_num [tilt_012_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_012_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_012_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_012_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_012_018]

def tilt_012_019 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(972291/5000000), (972291/5000000), (100247/1562500), (2259461/25000000), (2259461/25000000), (400831/4000000), (26596089/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(3295207/100000000), 0, (4092913/25000000), 0, 0]] i.1) i.2
    mu := ![(2081267/25000000), (1/100000000), (5398897/100000000), (2800617/100000000), (1/100000000), (3409791/100000000), (167473/100000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-439065566000266867795658171668672618850235029/2950813954313840649919735874100000000000000000), (-17492095219150550451897/3229176704575000000000), (-62844417542889654111917321772619658254284772529/1475406977156920324959867937050000000000000000), (-17492095219150550451897/3229176704575000000000), (-125249769519779041356038985373570643889719310029/2950813954313840649919735874100000000000000000)]
    bernstein := [(142163750030026779112132005871587290540051692812451/7554083723043432063794523837696000000000000000000000), (8506145353886237024738384370226532624476931923747/343367441956519639263387447168000000000000000000000), (148816071760398308133730196534154758200785889520017/5665562792282574047845892878272000000000000000000000), (2002708530405322556306467736872480693487842521083/85841860489129909815846861792000000000000000000000), (7542288747620585923345303176803071766966378026771/472130232690214503987157739856000000000000000000000)]
    reserve := (7987508769/500000000000) }

theorem tilt_012_019_valid : tilt_012_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_012_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_012_019]
  · intro i; fin_cases i <;> norm_num [tilt_012_019]
  · norm_num [tilt_012_019]
  · norm_num [tilt_012_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_012_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_012_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_012_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_012_019]

def tilt_012_020 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(972291/5000000), (972291/5000000), (100247/1562500), (2259461/25000000), (2259461/25000000), (400831/4000000), (26596089/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(415993/12500000), 0, (16365029/100000000), 0, 0]] i.1) i.2
    mu := ![(2081267/25000000), (1/100000000), (5398897/100000000), (2800617/100000000), (1/100000000), (3409791/100000000), (167473/100000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-437844917158163516004044370942732138382485029/2950813954313840649919735874100000000000000000), (-69968387420182900566549/12916706818300000000000), (-62843197247850751671833828636703981600598522529/1475406977156920324959867937050000000000000000), (-69968387420182900566549/12916706818300000000000), (-125248549578543339827663612902465231062814560029/2950813954313840649919735874100000000000000000)]
    bernstein := [(145324143009042414226014107581936157944569737562451/7554083723043432063794523837696000000000000000000000), (8649530731284651282030725889697607453136837673747/343367441956519639263387447168000000000000000000000), (151177990900172623774654497864714628227434967770017/5665562792282574047845892878272000000000000000000000), (2038442973076289358423411439860229677272324271083/85841860489129909815846861792000000000000000000000), (7738582007243826201291684438227165830049222776771/472130232690214503987157739856000000000000000000000)]
    reserve := (16390778373/1000000000000) }

theorem tilt_012_020_valid : tilt_012_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_012_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_012_020]
  · intro i; fin_cases i <;> norm_num [tilt_012_020]
  · norm_num [tilt_012_020]
  · norm_num [tilt_012_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_012_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_012_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_012_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_012_020]

def tiltBundle012_row : Alternative → Row
  | .zero => tilt_012_000
  | (.spike 0 false false) => tilt_012_001
  | (.spike 0 false true) => tilt_012_002
  | (.spike 0 true false) => tilt_012_003
  | (.spike 0 true true) => tilt_012_004
  | (.spike 1 false false) => tilt_012_005
  | (.spike 1 false true) => tilt_012_006
  | (.spike 1 true false) => tilt_012_007
  | (.spike 1 true true) => tilt_012_008
  | (.spike 2 false false) => tilt_012_009
  | (.spike 2 false true) => tilt_012_010
  | (.spike 2 true false) => tilt_012_011
  | (.spike 2 true true) => tilt_012_012
  | (.spike 3 false false) => tilt_012_013
  | (.spike 3 false true) => tilt_012_014
  | (.spike 3 true false) => tilt_012_015
  | (.spike 3 true true) => tilt_012_016
  | (.spike 4 false false) => tilt_012_017
  | (.spike 4 false true) => tilt_012_018
  | (.spike 4 true false) => tilt_012_019
  | (.spike 4 true true) => tilt_012_020

def tiltBundle012 : TiltBundle where
  interval := ⟨(-3/40), (-1/20)⟩
  lambda := ![(972291/5000000), (972291/5000000), (100247/1562500), (2259461/25000000), (2259461/25000000), (400831/4000000), (26596089/100000000)]
  row := tiltBundle012_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_012_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_012_001_valid | exact tilt_012_002_valid | exact tilt_012_003_valid | exact tilt_012_004_valid | exact tilt_012_005_valid | exact tilt_012_006_valid | exact tilt_012_007_valid | exact tilt_012_008_valid | exact tilt_012_009_valid | exact tilt_012_010_valid | exact tilt_012_011_valid | exact tilt_012_012_valid | exact tilt_012_013_valid | exact tilt_012_014_valid | exact tilt_012_015_valid | exact tilt_012_016_valid | exact tilt_012_017_valid | exact tilt_012_018_valid | exact tilt_012_019_valid | exact tilt_012_020_valid
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
