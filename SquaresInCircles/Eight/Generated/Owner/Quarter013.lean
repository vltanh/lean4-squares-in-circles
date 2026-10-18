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

def quarter_013_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 1, 0, 0, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (305109/781250), (476141/781250)]
    cone := fun i => (![![0, 0, (14961777/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(305109/1562500), 0, (305109/781250), 0, 0], ![0, 0, (46788991/100000000), 0, 0]] i.1) i.2
    mu := ![(13862837/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (341629/100000000)]
    alternative := .zero
    polynomial := [(-14374691271790946411340937/1183986785368250000000000), (-9297593879616/133448828125), (-63788844655569788786860937/591993392684125000000000), (-9297593879616/133448828125), (-113202998039348631162380937/1183986785368250000000000)]
    bernstein := [(2990005041502588170728626727/4849609872868352000000000000), (7620368667567275881374279419/12124024682170880000000000000), (57200606057925900106726513837/90930185116281600000000000000), (46860259961119773118474510947/75775154263568000000000000000), (113063918489006412728021519863/189437885658920000000000000000)]
    reserve := (14920975033/25000000000) }

theorem quarter_013_000_valid : quarter_013_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_013_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_013_000]
  · intro i; fin_cases i <;> norm_num [quarter_013_000]
  · norm_num [quarter_013_000]
  · norm_num [quarter_013_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_013_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_013_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_013_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_013_000]

def quarter_013_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (37732553/100000000), (62267447/100000000)]
    cone := fun i => (![![0, 0, (1528617/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(18866277/100000000), 0, (37732553/100000000), 0, 0], ![0, 0, (4953271/10000000), 0, 0]] i.1) i.2
    mu := ![(14163403/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (354441/100000000)]
    alternative := .zero
    polynomial := [(-107611658598710606406360499/10040181445446000000000000), (-2349509744102191/35444100000000), (-181483337459563315242486833/1673363574241000000000000), (-2349509744102191/35444100000000), (-981288366158669285048560499/10040181445446000000000000)]
    bernstein := [(919532253676100215105530441101/1606429031271360000000000000000), (1879851632914358466935883430559/3212858062542720000000000000000), (3767188926728837572299399960181/6425716125085440000000000000000), (7404713308036821615973784746679/12851432250170880000000000000000), (14266927128878180023579413088861/25702864500341760000000000000000)]
    reserve := (277535741759/500000000000) }

theorem quarter_013_001_valid : quarter_013_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_013_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_013_001]
  · intro i; fin_cases i <;> norm_num [quarter_013_001]
  · norm_num [quarter_013_001]
  · norm_num [quarter_013_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_013_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_013_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_013_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_013_001]

def quarter_013_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 1, 0, 0, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (36281179/100000000), (63718821/100000000)]
    cone := fun i => (![![0, 0, (15642471/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1814059/10000000), 0, (36281179/100000000), 0, 0], ![0, 0, (6547619/12500000), 0, 0]] i.1) i.2
    mu := ![(7246767/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (367987/100000000)]
    alternative := .zero
    polynomial := [(-8328927597030419362173933/888905349343000000000000), (-2311793950369959/36798700000000), (-48640910973048999170613933/444452674671500000000000), (-2311793950369959/36798700000000), (-88952894349067578979053933/888905349343000000000000)]
    bernstein := [(1201621007407386091306135973187/2275597694318080000000000000000), (308040043995528656192395392597/568899423579520000000000000000), (77265236295115823350674097207/142224855894880000000000000000), (18976090232022837413552977017/35556213973720000000000000000), (4559949838646291704679922027/8889053493430000000000000000)]
    reserve := (128246214347/250000000000) }

theorem quarter_013_002_valid : quarter_013_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_013_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_013_002]
  · intro i; fin_cases i <;> norm_num [quarter_013_002]
  · norm_num [quarter_013_002]
  · norm_num [quarter_013_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_013_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_013_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_013_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_013_002]

def quarter_013_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (34687529/100000000), (65312471/100000000)]
    cone := fun i => (![![0, 0, (32067399/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(3468753/20000000), 0, (34687529/100000000), 0, 0], ![0, 0, (27669903/50000000), 0, 0]] i.1) i.2
    mu := ![(14856027/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (95581/25000000)]
    alternative := .zero
    polynomial := [(-22993938576098725413408389/2839907833374000000000000), (-2265528231874159/38232400000000), (-157232236230409305195663389/1419953916687000000000000), (-2265528231874159/38232400000000), (-291470533884719884977918389/2839907833374000000000000)]
    bernstein := [(13721315095064621478401170291/28399078333740000000000000000), (56494547290367897220467356867/113596313334960000000000000000), (681225850798745907422906180437/1363155760019520000000000000000), (891783001585839687797971583423/1817541013359360000000000000000), (3418956771277319837318513405851/7270164053437440000000000000000)]
    reserve := (470272300067/1000000000000) }

theorem quarter_013_003_valid : quarter_013_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_013_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_013_003]
  · intro i; fin_cases i <;> norm_num [quarter_013_003]
  · norm_num [quarter_013_003]
  · norm_num [quarter_013_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_013_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_013_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_013_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_013_003]

def quarter_013_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 1, 0, 0, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (32937947/100000000), (67062053/100000000)]
    cone := fun i => (![![0, 0, (2057901/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(8234487/50000000), 0, (32937947/100000000), 0, 0], ![0, 0, (29207921/50000000), 0, 0]] i.1) i.2
    mu := ![(3813497/25000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (79503/20000000)]
    alternative := .zero
    polynomial := [(-522976290930603728141567/75796112997750000000000), (-2208886347425191/39751500000000), (-1419268948894550494390689/12632685499625000000000), (-2208886347425191/39751500000000), (-7992637402436699238202567/75796112997750000000000)]
    bernstein := [(84874092072739102667061094153/194038049274240000000000000000), (8777224093450606029420858503/19403804927424000000000000000), (294530147709546860396101443/646793497580800000000000000), (86680303311943665214532231/194038049274240000000000000), (8277382639847301395568137/19403804927424000000000000)]
    reserve := (426585541897/1000000000000) }

theorem quarter_013_004_valid : quarter_013_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_013_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_013_004]
  · intro i; fin_cases i <;> norm_num [quarter_013_004]
  · norm_num [quarter_013_004]
  · norm_num [quarter_013_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_013_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_013_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_013_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_013_004]

def quarter_013_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (31017243/100000000), (68982757/100000000)]
    cone := fun i => (![![0, 0, (8467363/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7754311/50000000), 0, (31017243/100000000), 0, 0], ![0, 0, (30808081/50000000), 0, 0]] i.1) i.2
    mu := ![(15690873/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (41363/10000000)]
    alternative := .zero
    polynomial := [(-3751957175530520117015977/649021579899000000000000), (-2139654936678951/41363000000000), (-5299802024152296461536711/46358684278500000000000), (-2139654936678951/41363000000000), (-70445271162601630344497977/649021579899000000000000)]
    bernstein := [(64865702008638222482352647/166149524454144000000000000), (674792094324244282489899079/1661495244541440000000000000), (20424339739921842881447883077/49844857336243200000000000000), (9529763332552959388327432721/23735646350592000000000000000), (633906697069892355947829894503/1661495244541440000000000000000)]
    reserve := (381527843159/1000000000000) }

theorem quarter_013_005_valid : quarter_013_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_013_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_013_005]
  · intro i; fin_cases i <;> norm_num [quarter_013_005]
  · norm_num [quarter_013_005]
  · norm_num [quarter_013_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_013_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_013_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_013_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_013_005]

def quarter_013_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 1, 0, 0, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (7227123/25000000), (17772877/25000000)]
    cone := fun i => (![![0, 0, (6980963/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7227123/50000000), 0, (7227123/25000000), 0, 0], ![0, 0, (32474227/50000000), 0, 0]] i.1) i.2
    mu := ![(16170531/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (430747/100000000)]
    alternative := .zero
    polynomial := [(-1270666289333411194334611/267900296794500000000000), (-128446768142871/2692168750000), (-15629113707204217875794611/133950148397250000000000), (-128446768142871/2692168750000), (-29987561125075024557254611/267900296794500000000000)]
    bernstein := [(234350765761282726162670766029/685824759793920000000000000000), (30712654145497541303502871981/85728094974240000000000000000), (2913139638542120547301436363/8037008903835000000000000000), (237453987474787426860471913/669750741986250000000000000), (14008069891154608198670741/41859421374140625000000000)]
    reserve := (41830696147/125000000000) }

theorem quarter_013_006_valid : quarter_013_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_013_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_013_006]
  · intro i; fin_cases i <;> norm_num [quarter_013_006]
  · norm_num [quarter_013_006]
  · norm_num [quarter_013_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_013_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_013_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_013_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_013_006]

def quarter_013_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (13296399/50000000), (36703601/50000000)]
    cone := fun i => (![![0, 0, (7208357/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(13296399/100000000), 0, (13296399/50000000), 0, 0], ![0, 0, (68421053/100000000), 0, 0]] i.1) i.2
    mu := ![(16697261/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (448949/100000000)]
    alternative := .zero
    polynomial := [(-11364612184292589064356729/2998487451475600000000000), (-488025723632799/11223725000000), (-179091873550159228802888729/1499243725737800000000000), (-488025723632799/11223725000000), (-346819134916025868541420729/2998487451475600000000000)]
    bernstein := [(136246441847856924563076799/468513664293062500000000000), (2310367049381714429525128261/7496218628689000000000000000), (28154514575963423602974382753/89954623544268000000000000000), (292980077649934007469982920953/959515984472192000000000000000), (2190905933801913779741503162471/7676127875777536000000000000000)]
    reserve := (57083622609/200000000000) }

theorem quarter_013_007_valid : quarter_013_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_013_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_013_007]
  · intro i; fin_cases i <;> norm_num [quarter_013_007]
  · norm_num [quarter_013_007]
  · norm_num [quarter_013_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_013_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_013_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_013_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_013_007]

def quarter_013_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 1, 0, 0, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (24049023/100000000), (75950977/100000000)]
    cone := fun i => (![![0, 0, (18645369/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(187883/1562500), 0, (24049023/100000000), 0, 0], ![0, 0, (72043011/100000000), 0, 0]] i.1) i.2
    mu := ![(1727587/10000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (468331/100000000)]
    alternative := .zero
    polynomial := [(-592130163232521009777523/202270636824250000000000), (-1826546792745471/46833100000000), (-12408257453348347240388773/101135318412125000000000), (-1826546792745471/46833100000000), (-24224384743464173471000023/202270636824250000000000)]
    bernstein := [(122784263339620107957711558377/517812830270080000000000000000), (66124220278493264215192924433/258906415135040000000000000000), (101259237814788241533305556971/388359622702560000000000000000), (104431986989384370034921429/412271361680000000000000000), (7548604663746480273710102537/32363301891880000000000000000)]
    reserve := (5831145327/25000000000) }

theorem quarter_013_008_valid : quarter_013_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_013_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_013_008]
  · intro i; fin_cases i <;> norm_num [quarter_013_008]
  · norm_num [quarter_013_008]
  · norm_num [quarter_013_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_013_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_013_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_013_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_013_008]

def quarter_013_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 1, 0, 0, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (664171/3125000), (2460829/3125000)]
    cone := fun i => (![![0, 0, (3866331/10000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(664171/6250000), 0, (664171/3125000), 0, 0], ![0, 0, (4739011/6250000), 0, 0]] i.1) i.2
    mu := ![(4477937/25000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (489/100000)]
    alternative := .zero
    polynomial := [(-4733832133543288874689/2189711193000000000000), (-1634411257759/47753906250), (-46140063934181650534123/364951865500000000000), (-1634411257759/47753906250), (-272106551471546614330049/2189711193000000000000)]
    bernstein := [(63056820484380790782766031/350353790880000000000000000), (9303894629255031036217799/46713838784000000000000000), (3831329916890693390789357/18685535513600000000000000), (295623248417801293123283/1494842841088000000000000), (63657156070695807467159/358762281861120000000000)]
    reserve := (44358868873/250000000000) }

theorem quarter_013_009_valid : quarter_013_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_013_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_013_009]
  · intro i; fin_cases i <;> norm_num [quarter_013_009]
  · norm_num [quarter_013_009]
  · norm_num [quarter_013_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_013_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_013_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_013_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_013_009]

def quarter_013_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 1, 0, 0, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (18179523/100000000), (81820477/100000000)]
    cone := fun i => (![![0, 0, (40172571/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(9089761/100000000), 0, (18179523/100000000), 0, 0], ![0, 0, (79775281/100000000), 0, 0]] i.1) i.2
    mu := ![(18610951/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (511071/100000000)]
    alternative := .zero
    polynomial := [(-9525812173751588768646093/6341011559014000000000000), (-495819081164157/17035700000000), (-1243361023064464170147808279/9511517338521000000000000), (-495819081164157/17035700000000), (-144596741741627857293510487/1119002039826000000000000)]
    bernstein := [(369664029148369400685842849/3116734001486561280000000000), (2702541507450695926369574213/19479587509291008000000000000), (53006201815115764320021341327/365242265799206400000000000000), (20988043749633593264040589501/152184277416336000000000000000), (22291761804267451665470075921/190230346770420000000000000000)]
    reserve := (29295748789/250000000000) }

theorem quarter_013_010_valid : quarter_013_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_013_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_013_010]
  · intro i; fin_cases i <;> norm_num [quarter_013_010]
  · norm_num [quarter_013_010]
  · norm_num [quarter_013_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_013_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_013_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_013_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_013_010]

def quarter_013_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 1]
    lambda := ![(23/25000000), (93/100000000), (31/50000000), (29/50000000), (9/25000000), (14797149/100000000), (8520251/10000000)]
    cone := fun i => (![![0, 0, (41833027/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7398557/100000000), 0, (14797113/100000000), 0, 0], ![0, 0, (83907759/100000000), 0, 0]] i.1) i.2
    mu := ![(19380241/100000000), (1/20000000), (29/100000000), (1/50000000), (9/50000000), (1/100000000), (21387/4000000)]
    alternative := .zero
    polynomial := [(-69214281975427849621125383/72120427282458000000000000), (-21012572251559/891125000000), (-4890834326988801173616585383/36060213641229000000000000), (-21012572251559/891125000000), (-9712454372002174497612045383/72120427282458000000000000)]
    bernstein := [(37570842354837125159586488017/721204272824580000000000000000), (211178075466655453015061455751/2884817091298320000000000000000), (2772161389014229719350666998759/34617805095579840000000000000000), (3362092830962107401473559037459/46157073460773120000000000000000), (9518060069191857160859580333577/184628293843092480000000000000000)]
    reserve := (6444069237/125000000000) }

theorem quarter_013_011_valid : quarter_013_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_013_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_013_011]
  · intro i; fin_cases i <;> norm_num [quarter_013_011]
  · norm_num [quarter_013_011]
  · norm_num [quarter_013_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_013_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_013_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_013_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_013_011]

def quarter_013_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 1, 0, 0, 0, 0, 1]
    lambda := ![(2331141/12500000), (8890263/50000000), (729731/6250000), (729731/6250000), (6150797/100000000), (6150797/100000000), (13958679/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (14199307/50000000), 0, 0]] i.1) i.2
    mu := ![(848331/10000000), (361199/50000000), (5374837/100000000), (1/100000000), (666911/20000000), (1/100000000), (432429/50000000)]
    alternative := .zero
    polynomial := [(-1359299674870502392144299660378534533/38804174518650917457699355237500000000), (-33744877024157/14414300000000), (-33534553830699121683200600053740007051/2425260907415682341106209702343750000), (-33744877024157/14414300000000), (-535193561616315444539065301199461578283/38804174518650917457699355237500000000)]
    bernstein := [(6290498858384331809226160508520829817063677/99338686767746348691710349408000000000000000), (17371181831642614585794677747355540954409/282212178317461217874177129000000000000000), (228803930606054835188270083306238275526011/3921263951358408500988566424000000000000000), (30320038171870233560450778763446209798683/564424356634922435748354258000000000000000), (17406983043688098125251846622692963983401/365215760175538046660699814000000000000000)]
    reserve := (47662190249/1000000000000) }

theorem quarter_013_012_valid : quarter_013_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_013_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_013_012]
  · intro i; fin_cases i <;> norm_num [quarter_013_012]
  · norm_num [quarter_013_012]
  · norm_num [quarter_013_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_013_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_013_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_013_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_013_012]

def quarter_013_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 1]
    lambda := ![(18550089/100000000), (18065003/100000000), (12656699/100000000), (12656699/100000000), (1393573/20000000), (1393573/20000000), (24135779/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3176951/12500000), 0, 0]] i.1) i.2
    mu := ![(7691779/100000000), (238981/50000000), (5573507/100000000), (1/100000000), (912677/25000000), (1/100000000), (1493053/100000000)]
    alternative := .zero
    polynomial := [(19660072181575975687116185311370105119097/13960824036925557493647657228733000000000000), (-222118863590153/149305300000000), (-77600455470762167939859534351553365238468403/6980412018462778746823828614366500000000000), (-222118863590153/149305300000000), (-155220571013705911855406184888418100582055903/13960824036925557493647657228733000000000000)]
    bernstein := [(107479587134840833250138246162968929054705341697/2233731845908089198983625156597280000000000000000), (204304494176777619068257193459521081483445150497/4467463691816178397967250313194560000000000000000), (1131016118758504218412415874004658234318294076691/26804782150897070387803501879167360000000000000000), (670266378685982584334290378860150173778379486897/17869854767264713591869001252778240000000000000000), (1131917278348243699645158884756218840175060574497/35739709534529427183738002505556480000000000000000)]
    reserve := (7917784539/250000000000) }

theorem quarter_013_013_valid : quarter_013_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_013_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_013_013]
  · intro i; fin_cases i <;> norm_num [quarter_013_013]
  · norm_num [quarter_013_013]
  · norm_num [quarter_013_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_013_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_013_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_013_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_013_013]

def quarter_013_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 1, 0, 0, 0, 0, 1]
    lambda := ![(9198429/50000000), (3649173/20000000), (13491331/100000000), (13491331/100000000), (7697467/100000000), (7697467/100000000), (20979679/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (14279/62500), 0, 0]] i.1) i.2
    mu := ![(7050593/100000000), (234523/100000000), (5733819/100000000), (1/100000000), (3924821/100000000), (1/100000000), (2001373/100000000)]
    alternative := .zero
    polynomial := [(52231191327933138723666456163891852968611/3385168384747228126199696905861500000000000), (-234523949918383/200137300000000), (-28226861194708485953778339583477400411456389/1692584192373614063099848452930750000000000), (-234523949918383/200137300000000), (-56505953580744905046280345623118692675881389/3385168384747228126199696905861500000000000)]
    bernstein := [(297362754162672674065283001753413387846514433811/8666031064952904003071224079005440000000000000000), (697486401627041578748586607654923153306613969/21665077662382260007678060197513600000000000000), (460490383231661403364387021945677926307776411/16248808246786695005758545148135200000000000000), (308094567833520397996568479631598425403569/13540673538988912504798787623446000000000000), (52231191327933138723666456163891852968611/3385168384747228126199696905861500000000000)]
    reserve := (7714710967/500000000000) }

theorem quarter_013_014_valid : quarter_013_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_013_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_013_014]
  · intro i; fin_cases i <;> norm_num [quarter_013_014]
  · norm_num [quarter_013_014]
  · norm_num [quarter_013_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_013_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_013_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_013_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_013_014]

def quarter_013_015 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 1]
    lambda := ![(18452803/100000000), (1845857/10000000), (139417/1000000), (139417/1000000), (806527/10000000), (806527/10000000), (19074687/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(28837/6250000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (851981/4000000), 0, 0]] i.1) i.2
    mu := ![(6706023/100000000), (58297/50000000), (1461249/25000000), (1/100000000), (4069793/100000000), (1/100000000), (2348541/100000000)]
    alternative := .zero
    polynomial := [(22860815028398878379505900623746534939/1196617830562655259833192769000000000000), (521284999155595849/1140940788975000000), (-18490895123486615825792336213777728015061/598308915281327629916596384500000000000), (521284999155595849/1140940788975000000), (-37004651062001630529964178328179202565061/1196617830562655259833192769000000000000)]
    bernstein := [(22860815028398878379505900623746534939/1196617830562655259833192769000000000000), (341611864316085639962680039588401970957/15556031797314518377831505997000000000000), (1612577403057006127025259810347764676797807/74668952627109688213591228785600000000000000), (448389828199438625719147456628842839952157/24889650875703229404530409595200000000000000), (446263716681783857672710027620432380137236607/39823441401125167047248655352320000000000000000)]
    reserve := (2241211211/200000000000) }

theorem quarter_013_015_valid : quarter_013_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_013_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_013_015]
  · intro i; fin_cases i <;> norm_num [quarter_013_015]
  · norm_num [quarter_013_015]
  · norm_num [quarter_013_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_013_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_013_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_013_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_013_015]

def quarter_013_016 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 1, 0, 0, 0, 0, 1]
    lambda := ![(11593623/50000000), (2906569/12500000), (17078609/100000000), (17078609/100000000), (2425373/25000000), (2425373/25000000), 0]
    cone := fun i => (![![0, 0, 0, (11593623/100000000), 0], ![(435373/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (633397/25000000), 0, 0]] i.1) i.2
    mu := ![(2071453/50000000), (73369/50000000), (7289983/100000000), (1/100000000), (2481537/50000000), (1/100000000), (2533589/100000000)]
    alternative := .zero
    polynomial := [(-30138832031367954257489961690294130468461/1160966982180871783381819299830500000000000), (1265441665237/458556250000), (-21358970728227023863689212428415982334528461/580483491090435891690909649915250000000000), (1265441665237/458556250000), (-42687802624422679773120934895141670538588461/1160966982180871783381819299830500000000000)]
    bernstein := [(59626430071888615874305453756421729921319776339/2972075474383031765457457407566080000000000000000), (38383387121604021302437887137316094256031425139/1486037737191515882728728703783040000000000000000), (20634264036167588016588413201003309896244239139/743018868595757941364364351891520000000000000000), (9615828283445247580994595566285025479385738339/371509434297878970682182175945760000000000000000), (3742634206284058878695603981515828767929682739/185754717148939485341091087972880000000000000000)]
    reserve := (20062219343/1000000000000) }

theorem quarter_013_016_valid : quarter_013_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_013_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_013_016]
  · intro i; fin_cases i <;> norm_num [quarter_013_016]
  · norm_num [quarter_013_016]
  · norm_num [quarter_013_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_013_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_013_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_013_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_013_016]

def quarter_013_017 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 1]
    lambda := ![(2385791/10000000), (24045031/100000000), (16808743/100000000), (16808743/100000000), (4619893/50000000), (4619893/50000000), 0]
    cone := fun i => (![![0, 0, 0, (2385791/20000000), 0], ![(1496967/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2413011/100000000), 0, 0]] i.1) i.2
    mu := ![(852547/20000000), (9463/6250000), (1853259/25000000), (1/100000000), (2423317/50000000), (1/100000000), (603253/25000000)]
    alternative := .zero
    polynomial := [(-9696502323425157216412116854170010755577/87428494324149216798208153596000000000000), (35994617920977/7570400000000), (-1665969486244587700259110798018812126168077/43714247162074608399104076798000000000000), (35994617920977/7570400000000), (-3322242470165750243301809479183454241580577/87428494324149216798208153596000000000000)]
    bernstein := [(446312200173613805461487994996701829943737823/13988559091863874687713304575360000000000000000), (1060533884928573646428162596494930450267739269/27977118183727749375426609150720000000000000000), (352988234592558958179970043222619525602852359/8834879426440341908029455521280000000000000000), (4256400114644340421258326860164158214296865421/111908472734910997501706436602880000000000000000), (7189756131552131774785261669886459497967635663/223816945469821995003412873205760000000000000000)]
    reserve := (31905516303/1000000000000) }

theorem quarter_013_017_valid : quarter_013_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_013_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_013_017]
  · intro i; fin_cases i <;> norm_num [quarter_013_017]
  · norm_num [quarter_013_017]
  · norm_num [quarter_013_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_013_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_013_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_013_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_013_017]

def quarter_013_018 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 1, 0, 0, 0, 0, 1]
    lambda := ![0, (33134521/100000000), (4374083/20000000), (4374083/20000000), (2890581/25000000), (2890581/25000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(3693017/50000000), 0, (32631003/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3019553/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (207931/100000000), (10031783/100000000), (1/100000000), (625097/10000000), (1/100000000), (3019553/100000000)]
    alternative := .zero
    polynomial := [(-3321771775172259783741409971966231473/9449279271611907825664063200000000000), (3813441319439717/415862000000000), (-248996546606900252970129259646950899473/4724639635805953912832031600000000000), (3813441319439717/415862000000000), (-494671321438628246156517109321935567473/9449279271611907825664063200000000000)]
    bernstein := [(1015398274059786663960624280348537862228287/24190154935326484033700001792000000000000000), (304161890611572844767478377848878161440029/6047538733831621008425000448000000000000000), (241096054908894051052076555722222949363329/4535654050373715756318750336000000000000000), (19099608550064258820239195309572692835481/377971170864476313026562528000000000000000), (4004388031780393939014286969779944419927/94492792716119078256640632000000000000000)]
    reserve := (41975682949/1000000000000) }

theorem quarter_013_018_valid : quarter_013_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_013_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_013_018]
  · intro i; fin_cases i <;> norm_num [quarter_013_018]
  · norm_num [quarter_013_018]
  · norm_num [quarter_013_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_013_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_013_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_013_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_013_018]

def quarter_013_019 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 1, 0, 0, 0, 0, 1]
    lambda := ![0, (34929533/100000000), (21611889/100000000), (21611889/100000000), (2184669/20000000), (2184669/20000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(4731871/50000000), 0, (34056429/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (71317/2500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (218179/100000000), (10378801/100000000), (1/100000000), (6118787/100000000), (1/100000000), (2852681/100000000)]
    alternative := .zero
    polynomial := [(-23114657107983241539541144302821526397/36485186493567153004599612000000000000), (5421706609232063/436358000000000), (-1017753728312139366561845564164492506397/18242593246783576502299806000000000000), (5421706609232063/436358000000000), (-2012392799516295491584149984026163486397/36485186493567153004599612000000000000)]
    bernstein := [(21148508982347656850976261862594383084203/364851864935671530045996120000000000000000), (6502496651591352559680561296709090738381/97293830649512408012265632000000000000000), (48990307468918922725466600018544661256261/700515580676489337688312550400000000000000), (64404457527751449804545472643398378681/957970024856737555813076992000000000000), (2074906096290917727140848287297272003/35371200917787232830021304320000000000)]
    reserve := (57964645421/1000000000000) }

theorem quarter_013_019_valid : quarter_013_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_013_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_013_019]
  · intro i; fin_cases i <;> norm_num [quarter_013_019]
  · norm_num [quarter_013_019]
  · norm_num [quarter_013_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_013_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_013_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_013_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_013_019]

def quarter_013_020 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 1, 0, 0, 0, 0, 1]
    lambda := ![0, (183849/500000), (5330753/25000000), (5330753/25000000), (1286511/12500000), (1286511/12500000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1169433/10000000), 0, (35405241/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (107513/4000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (228333/100000000), (2148041/20000000), (1/100000000), (1495673/25000000), (1/100000000), (107513/4000000)]
    alternative := .zero
    polynomial := [(-2183710099251380734545565877363267/2146107835213267749404000000000000), (12163533123597/761110000000), (-63364021654859229347324200769363267/1073053917606633874702000000000000), (12163533123597/761110000000), (-124544333210467077960102835661363267/2146107835213267749404000000000000)]
    bernstein := [(3743665069901234773205898606835411/50231186817334541151764480000000000), (369174492065566474946102933380757227/4395228846516772350779392000000000000), (2057120875300548407298503917444952137/23545868820625566164889600000000000000), (11619097222904735367078278579556278911/137350901453649135961856000000000000000), (25960679951135265177986155765723332973/343377253634122839904640000000000000000)]
    reserve := (74528700337/1000000000000) }

theorem quarter_013_020_valid : quarter_013_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_013_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_013_020]
  · intro i; fin_cases i <;> norm_num [quarter_013_020]
  · norm_num [quarter_013_020]
  · norm_num [quarter_013_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_013_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_013_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_013_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_013_020]

def quarter_013_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 1]
    lambda := ![0, (38646681/100000000), (21004097/100000000), (21004097/100000000), (4836281/50000000), (4836281/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(2813989/20000000), 0, (36658163/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2526033/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (47661/20000000), (1389287/12500000), (1/100000000), (2921517/50000000), (1/100000000), (2526033/100000000)]
    alternative := .zero
    polynomial := [(-20715855471510681485111770189781/13670303169986360676000000000000), (3152805730181299/158870000000000), (-427063639982360872102975318537781/6835151584993180338000000000000), (3152805730181299/158870000000000), (-833411424493211062720838866885781/13670303169986360676000000000000)]
    bernstein := [(200550227948261528630159520896876539/2187248507197817708160000000000000000), (445325697640610147415663195959601791/4374497014395635416320000000000000000), (2768394153650915968141280760336142537/26246982086373812497920000000000000000), (1796137973915844629272710677309444551/17497988057582541665280000000000000000), (3262735828022276337207388433276763019/34995976115165083330560000000000000000)]
    reserve := (91690645707/1000000000000) }

theorem quarter_013_021_valid : quarter_013_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_013_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_013_021]
  · intro i; fin_cases i <;> norm_num [quarter_013_021]
  · norm_num [quarter_013_021]
  · norm_num [quarter_013_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_013_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_013_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_013_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_013_021]

def quarter_013_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 1, 0, 0, 0, 0, 1]
    lambda := ![0, (20274879/50000000), (10328153/50000000), (10328153/50000000), (1813763/20000000), (1813763/20000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(2072437/12500000), 0, (7559087/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1184181/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (247997/100000000), (11498927/100000000), (1/100000000), (5700309/100000000), (1/100000000), (1184181/50000000)]
    alternative := .zero
    polynomial := [(-18300030283928642362135756017054215303/8555348655354425692303756000000000000), (1191329526848463/49599400000000), (-282655867793628288074297280530644415303/4277674327677212846151878000000000000), (1191329526848463/49599400000000), (-547011705303327933786458805044234615303/8555348655354425692303756000000000000)]
    bernstein := [(2397497090885194973240611446779093979867097/21901692557707329772297615360000000000000000), (329257169137997375799219115119325144603071/2737711569713416221537201920000000000000000), (31896480603070711340890052982111050503171/256660459660632770769112680000000000000000), (2596728413934643588332917107762226769627/21388371638386064230759390000000000000000), (149132496614350198710726020800017663793/1336773227399129014422461875000000000000)]
    reserve := (4378651713/40000000000) }

theorem quarter_013_022_valid : quarter_013_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_013_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_013_022]
  · intro i; fin_cases i <;> norm_num [quarter_013_022]
  · norm_num [quarter_013_022]
  · norm_num [quarter_013_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_013_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_013_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_013_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_013_022]

def quarter_013_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 1]
    lambda := ![0, (4246681/10000000), (10140869/50000000), (10140869/50000000), (8484857/100000000), (8484857/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1920847/10000000), 0, (38797231/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1107929/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (64327/25000000), (2972871/25000000), (1/100000000), (2777589/50000000), (1/100000000), (2215859/100000000)]
    alternative := .zero
    polynomial := [(-6067909386242780165747891504948600761/2092458922157237035306608000000000000), (1466685428021089/51461600000000), (-73060076344373800697945701381900400761/1046229461078618517653304000000000000), (1466685428021089/51461600000000), (-140052243302504821230143511258852200761/2092458922157237035306608000000000000)]
    bernstein := [(41804636726016129082146104235009721391/326946706587068286766657500000000000000), (66293838501969060180133282950647162033/475558845944826598933320000000000000000), (9025236501194948074499065147439411651813/62773767664717111059198240000000000000000), (8575707576602955237826603755971173969421/60871532280937804663464960000000000000000), (699595945534794041344416447939574876595879/5356694840722526810384916480000000000000000)]
    reserve := (63931882297/500000000000) }

theorem quarter_013_023_valid : quarter_013_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_013_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_013_023]
  · intro i; fin_cases i <;> norm_num [quarter_013_023]
  · norm_num [quarter_013_023]
  · norm_num [quarter_013_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_013_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_013_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_013_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_013_023]

def quarter_013_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 1, 0, 0, 0, 0, 1]
    lambda := ![0, (2219193/5000000), (3976701/20000000), (3976701/20000000), (1584913/20000000), (1584913/20000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(21938861/100000000), 0, (7928831/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (413907/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (66533/25000000), (6144439/50000000), (1/100000000), (5408489/100000000), (1/100000000), (64673/3125000)]
    alternative := .zero
    polynomial := [(-3734653128682012345098628247512133663/980531383876462837040496000000000000), (177150660783309/5322640000000), (-36149101879254991909706711263474133663/490265691938231418520248000000000000), (177150660783309/5322640000000), (-68563550629827971474314794279436133663/980531383876462837040496000000000000)]
    bernstein := [(368699295287448189542748041096190920307457/2510160342723744862823669760000000000000000), (39962353776567191934651473699517867211993/251016034272374486282366976000000000000000), (12347664737982423591184002726226204814563/75304810281712345884710092800000000000000), (404304428997384331392989810454604586201/2510160342723744862823669760000000000000), (37741106061766226720699528866342171393/251016034272374486282366976000000000000)]
    reserve := (9180172901/62500000000) }

theorem quarter_013_024_valid : quarter_013_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_013_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_013_024]
  · intro i; fin_cases i <;> norm_num [quarter_013_024]
  · norm_num [quarter_013_024]
  · norm_num [quarter_013_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_013_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_013_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_013_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_013_024]

def quarter_013_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 1]
    lambda := ![0, (11571329/25000000), (4866439/25000000), (4866439/25000000), (3695793/50000000), (3695793/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(12374607/50000000), 0, (40317819/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (965173/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (6859/2500000), (12687571/100000000), (1/100000000), (1315319/25000000), (1/100000000), (965173/50000000)]
    alternative := .zero
    polynomial := [(-17236063788343988450493085074064892021/3535293906794014096622176000000000000), (5261095205496669/137180000000000), (-137466659464389702862593181109383724021/1767646953397007048311088000000000000), (5261095205496669/137180000000000), (-257697255140435417274693277144702556021/3535293906794014096622176000000000000)]
    bernstein := [(150701213391511875298408069798763172331/905035240139267608735277056000000000000), (1625958829152699527004131015838124698153/9050352401392676087352770560000000000000), (50188115994375262723761838068657020342281/271510572041780282620583116800000000000000), (164672612097567274882622780587948386652689/905035240139267608735277056000000000000000), (1545846770468177370167712281874253764397339/9050352401392676087352770560000000000000000)]
    reserve := (166514193821/1000000000000) }

theorem quarter_013_025_valid : quarter_013_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_013_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_013_025]
  · intro i; fin_cases i <;> norm_num [quarter_013_025]
  · norm_num [quarter_013_025]
  · norm_num [quarter_013_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_013_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_013_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_013_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_013_025]

def quarter_013_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 1, 0, 0, 0, 0, 1]
    lambda := ![0, (48154213/100000000), (4758413/25000000), (4758413/25000000), (6889241/100000000), (6889241/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1725927/6250000), 0, (4080147/10000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (449789/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (70471/25000000), (13083623/100000000), (1/100000000), (5114767/100000000), (1/100000000), (1799157/100000000)]
    alternative := .zero
    polynomial := [(-29613328302449442923218712384206394551/4848365191134541549136244000000000000), (2463064736465121/56376800000000), (-198581538141577414077934676447531444551/2424182595567270774568122000000000000), (2463064736465121/56376800000000), (-367549747980705385232650640510856494551/4848365191134541549136244000000000000)]
    bernstein := [(2317779854270524232758239090360460970771609/12411814889304426365788784640000000000000000), (622899681451003321755592055388431453019157/3102953722326106591447196160000000000000000), (480306511549420572373149194958894721102583/2327215291744579943585397120000000000000000), (39468172387342765837939526594142398613953/193934607645381661965449760000000000000000), (9305825237405616986397444197772478089569/48483651911345415491362440000000000000000)]
    reserve := (3734796039/20000000000) }

theorem quarter_013_026_valid : quarter_013_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_013_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_013_026]
  · intro i; fin_cases i <;> norm_num [quarter_013_026]
  · norm_num [quarter_013_026]
  · norm_num [quarter_013_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_013_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_013_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_013_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_013_026]

def quarter_013_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 1]
    lambda := ![0, (49972563/100000000), (18593287/100000000), (18593287/100000000), (6420431/100000000), (6420431/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(30508161/100000000), 0, (5135081/12500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (419181/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1443/500000), (13472767/100000000), (1/100000000), (2485183/50000000), (1/100000000), (67069/4000000)]
    alternative := .zero
    polynomial := [(-973741231830344435783742604997269/129617406277152180867480000000000), (2369876223456003/48100000000000), (-1116758837024087331611616171873257/12961740627715218086748000000000), (2369876223456003/48100000000000), (-10193847138410528880332419113735301/129617406277152180867480000000000)]
    bernstein := [(20692137308340469467707793804667259/99705697136270908359600000000000000), (288311010461522986987079169834557957/1296174062771521808674800000000000000), (2031389994025224223298329472095030841/8888050716147578116627200000000000000), (1872444807463590063386775361727143957/8295514001737739575518720000000000000), (70916658435828229880415455836597099451/331820560069509583020748800000000000000)]
    reserve := (51883036533/250000000000) }

theorem quarter_013_027_valid : quarter_013_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_013_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_013_027]
  · intro i; fin_cases i <;> norm_num [quarter_013_027]
  · norm_num [quarter_013_027]
  · norm_num [quarter_013_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_013_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_013_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_013_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_013_027]

def quarter_013_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 1, 0, 0, 0, 0, 1]
    lambda := ![0, (51721811/100000000), (1134471/6250000), (1134471/6250000), (5987559/100000000), (5987559/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(33399347/100000000), 0, (41143833/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (781839/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (294413/100000000), (2770103/20000000), (1/100000000), (4829621/100000000), (1/100000000), (781839/50000000)]
    alternative := .zero
    polynomial := [(-118525175960814156336139860160706661/13035012879146902505495200000000000), (32421460706906777/588826000000000), (-589614169768756268997364367839982661/6517506439573451252747600000000000), (32421460706906777/588826000000000), (-1060703163576698381658588875519258661/13035012879146902505495200000000000)]
    bernstein := [(7636800844610481304117185899284653306379/33369632970616070414067712000000000000000), (4082445919596305306876151740840185953681/16684816485308035207033856000000000000000), (2096467793636994787376354087348953219859/8342408242654017603516928000000000000000), (1036640867857035449866374640183062533001/4171204121327008801758464000000000000000), (492436658320852746950116239252777427739/2085602060663504400879232000000000000000)]
    reserve := (114427402473/500000000000) }

theorem quarter_013_028_valid : quarter_013_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_013_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_013_028]
  · intro i; fin_cases i <;> norm_num [quarter_013_028]
  · norm_num [quarter_013_028]
  · norm_num [quarter_013_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_013_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_013_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_013_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_013_028]

def quarter_013_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 1, 0, 0, 0, 0, 1]
    lambda := ![0, (427067/800000), (17715841/100000000), (17715841/100000000), (699059/12500000), (699059/12500000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(36256977/100000000), 0, (40983039/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1460499/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (299237/100000000), (14212291/100000000), (1/100000000), (938837/20000000), (1/100000000), (2921/200000)]
    alternative := .zero
    polynomial := [(-22007801783707077386179835552179797/2028305146259690448532000000000000), (292180664412567/4787792000000), (-96155588394266762057444036844679797/1014152573129845224266000000000000), (292180664412567/4787792000000), (-170303375004826446728708238137179797/2028305146259690448532000000000000)]
    bernstein := [(81347341477994959012070053721060745003/324528823401550471765120000000000000000), (34716501501065349783182103001778327607/129811529360620188706048000000000000000), (14257585355966719306340399235604544899/51924611744248075482419200000000000000), (5646825760973995445840848682105092239/20769844697699230192967680000000000000), (2152299232866393050729433685202861787/8307937879079692077187072000000000000)]
    reserve := (31332864607/125000000000) }

theorem quarter_013_029_valid : quarter_013_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_013_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_013_029]
  · intro i; fin_cases i <;> norm_num [quarter_013_029]
  · norm_num [quarter_013_029]
  · norm_num [quarter_013_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_013_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_013_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_013_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_013_029]

def quarterTable013 : OwnerTable where
  mode := .quarter
  owners := ![0, 1, 0, 0, 0, 0, 1]
  rows := [quarter_013_000, quarter_013_001, quarter_013_002, quarter_013_003, quarter_013_004, quarter_013_005, quarter_013_006, quarter_013_007, quarter_013_008, quarter_013_009, quarter_013_010, quarter_013_011, quarter_013_012, quarter_013_013, quarter_013_014, quarter_013_015, quarter_013_016, quarter_013_017, quarter_013_018, quarter_013_019, quarter_013_020, quarter_013_021, quarter_013_022, quarter_013_023, quarter_013_024, quarter_013_025, quarter_013_026, quarter_013_027, quarter_013_028, quarter_013_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_013_000_valid
    · exact quarter_013_001_valid
    · exact quarter_013_002_valid
    · exact quarter_013_003_valid
    · exact quarter_013_004_valid
    · exact quarter_013_005_valid
    · exact quarter_013_006_valid
    · exact quarter_013_007_valid
    · exact quarter_013_008_valid
    · exact quarter_013_009_valid
    · exact quarter_013_010_valid
    · exact quarter_013_011_valid
    · exact quarter_013_012_valid
    · exact quarter_013_013_valid
    · exact quarter_013_014_valid
    · exact quarter_013_015_valid
    · exact quarter_013_016_valid
    · exact quarter_013_017_valid
    · exact quarter_013_018_valid
    · exact quarter_013_019_valid
    · exact quarter_013_020_valid
    · exact quarter_013_021_valid
    · exact quarter_013_022_valid
    · exact quarter_013_023_valid
    · exact quarter_013_024_valid
    · exact quarter_013_025_valid
    · exact quarter_013_026_valid
    · exact quarter_013_027_valid
    · exact quarter_013_028_valid
    · exact quarter_013_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
