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

def quarter_037_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 3, 0, 0, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (305109/781250), (476141/781250)]
    cone := fun i => (![![0, 0, (14961777/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(305109/1562500), 0, (305109/781250), 0, 0], ![0, 0, (46788991/100000000), 0, 0]] i.1) i.2
    mu := ![(13862837/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (341629/100000000)]
    alternative := .zero
    polynomial := [(-14374691271790946411340937/1183986785368250000000000), (-9297593879616/133448828125), (-63788844655569788786860937/591993392684125000000000), (-9297593879616/133448828125), (-113202998039348631162380937/1183986785368250000000000)]
    bernstein := [(2990005041502588170728626727/4849609872868352000000000000), (7620368667567275881374279419/12124024682170880000000000000), (57200606057925900106726513837/90930185116281600000000000000), (46860259961119773118474510947/75775154263568000000000000000), (113063918489006412728021519863/189437885658920000000000000000)]
    reserve := (14920975033/25000000000) }

theorem quarter_037_000_valid : quarter_037_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_037_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_037_000]
  · intro i; fin_cases i <;> norm_num [quarter_037_000]
  · norm_num [quarter_037_000]
  · norm_num [quarter_037_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_037_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_037_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_037_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_037_000]

def quarter_037_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (37732553/100000000), (62267447/100000000)]
    cone := fun i => (![![0, 0, (1528617/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(18866277/100000000), 0, (37732553/100000000), 0, 0], ![0, 0, (4953271/10000000), 0, 0]] i.1) i.2
    mu := ![(14163403/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (354441/100000000)]
    alternative := .zero
    polynomial := [(-107611658598710606406360499/10040181445446000000000000), (-2349509744102191/35444100000000), (-181483337459563315242486833/1673363574241000000000000), (-2349509744102191/35444100000000), (-981288366158669285048560499/10040181445446000000000000)]
    bernstein := [(919532253676100215105530441101/1606429031271360000000000000000), (1879851632914358466935883430559/3212858062542720000000000000000), (3767188926728837572299399960181/6425716125085440000000000000000), (7404713308036821615973784746679/12851432250170880000000000000000), (14266927128878180023579413088861/25702864500341760000000000000000)]
    reserve := (277535741759/500000000000) }

theorem quarter_037_001_valid : quarter_037_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_037_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_037_001]
  · intro i; fin_cases i <;> norm_num [quarter_037_001]
  · norm_num [quarter_037_001]
  · norm_num [quarter_037_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_037_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_037_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_037_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_037_001]

def quarter_037_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 3, 0, 0, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (36281179/100000000), (63718821/100000000)]
    cone := fun i => (![![0, 0, (15642471/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1814059/10000000), 0, (36281179/100000000), 0, 0], ![0, 0, (6547619/12500000), 0, 0]] i.1) i.2
    mu := ![(7246767/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (367987/100000000)]
    alternative := .zero
    polynomial := [(-8328927597030419362173933/888905349343000000000000), (-2311793950369959/36798700000000), (-48640910973048999170613933/444452674671500000000000), (-2311793950369959/36798700000000), (-88952894349067578979053933/888905349343000000000000)]
    bernstein := [(1201621007407386091306135973187/2275597694318080000000000000000), (308040043995528656192395392597/568899423579520000000000000000), (77265236295115823350674097207/142224855894880000000000000000), (18976090232022837413552977017/35556213973720000000000000000), (4559949838646291704679922027/8889053493430000000000000000)]
    reserve := (128246214347/250000000000) }

theorem quarter_037_002_valid : quarter_037_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_037_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_037_002]
  · intro i; fin_cases i <;> norm_num [quarter_037_002]
  · norm_num [quarter_037_002]
  · norm_num [quarter_037_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_037_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_037_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_037_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_037_002]

def quarter_037_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (34687529/100000000), (65312471/100000000)]
    cone := fun i => (![![0, 0, (32067399/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(3468753/20000000), 0, (34687529/100000000), 0, 0], ![0, 0, (27669903/50000000), 0, 0]] i.1) i.2
    mu := ![(14856027/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (95581/25000000)]
    alternative := .zero
    polynomial := [(-22993938576098725413408389/2839907833374000000000000), (-2265528231874159/38232400000000), (-157232236230409305195663389/1419953916687000000000000), (-2265528231874159/38232400000000), (-291470533884719884977918389/2839907833374000000000000)]
    bernstein := [(13721315095064621478401170291/28399078333740000000000000000), (56494547290367897220467356867/113596313334960000000000000000), (681225850798745907422906180437/1363155760019520000000000000000), (891783001585839687797971583423/1817541013359360000000000000000), (3418956771277319837318513405851/7270164053437440000000000000000)]
    reserve := (470272300067/1000000000000) }

theorem quarter_037_003_valid : quarter_037_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_037_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_037_003]
  · intro i; fin_cases i <;> norm_num [quarter_037_003]
  · norm_num [quarter_037_003]
  · norm_num [quarter_037_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_037_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_037_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_037_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_037_003]

def quarter_037_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 3, 0, 0, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (32937947/100000000), (67062053/100000000)]
    cone := fun i => (![![0, 0, (2057901/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(8234487/50000000), 0, (32937947/100000000), 0, 0], ![0, 0, (29207921/50000000), 0, 0]] i.1) i.2
    mu := ![(3813497/25000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (79503/20000000)]
    alternative := .zero
    polynomial := [(-522976290930603728141567/75796112997750000000000), (-2208886347425191/39751500000000), (-1419268948894550494390689/12632685499625000000000), (-2208886347425191/39751500000000), (-7992637402436699238202567/75796112997750000000000)]
    bernstein := [(84874092072739102667061094153/194038049274240000000000000000), (8777224093450606029420858503/19403804927424000000000000000), (294530147709546860396101443/646793497580800000000000000), (86680303311943665214532231/194038049274240000000000000), (8277382639847301395568137/19403804927424000000000000)]
    reserve := (426585541897/1000000000000) }

theorem quarter_037_004_valid : quarter_037_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_037_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_037_004]
  · intro i; fin_cases i <;> norm_num [quarter_037_004]
  · norm_num [quarter_037_004]
  · norm_num [quarter_037_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_037_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_037_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_037_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_037_004]

def quarter_037_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (31017243/100000000), (68982757/100000000)]
    cone := fun i => (![![0, 0, (8467363/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7754311/50000000), 0, (31017243/100000000), 0, 0], ![0, 0, (30808081/50000000), 0, 0]] i.1) i.2
    mu := ![(15690873/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (41363/10000000)]
    alternative := .zero
    polynomial := [(-3751957175530520117015977/649021579899000000000000), (-2139654936678951/41363000000000), (-5299802024152296461536711/46358684278500000000000), (-2139654936678951/41363000000000), (-70445271162601630344497977/649021579899000000000000)]
    bernstein := [(64865702008638222482352647/166149524454144000000000000), (674792094324244282489899079/1661495244541440000000000000), (20424339739921842881447883077/49844857336243200000000000000), (9529763332552959388327432721/23735646350592000000000000000), (633906697069892355947829894503/1661495244541440000000000000000)]
    reserve := (381527843159/1000000000000) }

theorem quarter_037_005_valid : quarter_037_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_037_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_037_005]
  · intro i; fin_cases i <;> norm_num [quarter_037_005]
  · norm_num [quarter_037_005]
  · norm_num [quarter_037_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_037_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_037_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_037_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_037_005]

def quarter_037_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 3, 0, 0, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (7227123/25000000), (17772877/25000000)]
    cone := fun i => (![![0, 0, (6980963/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7227123/50000000), 0, (7227123/25000000), 0, 0], ![0, 0, (32474227/50000000), 0, 0]] i.1) i.2
    mu := ![(16170531/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (430747/100000000)]
    alternative := .zero
    polynomial := [(-1270666289333411194334611/267900296794500000000000), (-128446768142871/2692168750000), (-15629113707204217875794611/133950148397250000000000), (-128446768142871/2692168750000), (-29987561125075024557254611/267900296794500000000000)]
    bernstein := [(234350765761282726162670766029/685824759793920000000000000000), (30712654145497541303502871981/85728094974240000000000000000), (2913139638542120547301436363/8037008903835000000000000000), (237453987474787426860471913/669750741986250000000000000), (14008069891154608198670741/41859421374140625000000000)]
    reserve := (41830696147/125000000000) }

theorem quarter_037_006_valid : quarter_037_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_037_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_037_006]
  · intro i; fin_cases i <;> norm_num [quarter_037_006]
  · norm_num [quarter_037_006]
  · norm_num [quarter_037_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_037_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_037_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_037_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_037_006]

def quarter_037_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (13296399/50000000), (36703601/50000000)]
    cone := fun i => (![![0, 0, (7208357/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(13296399/100000000), 0, (13296399/50000000), 0, 0], ![0, 0, (68421053/100000000), 0, 0]] i.1) i.2
    mu := ![(16697261/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (448949/100000000)]
    alternative := .zero
    polynomial := [(-11364612184292589064356729/2998487451475600000000000), (-488025723632799/11223725000000), (-179091873550159228802888729/1499243725737800000000000), (-488025723632799/11223725000000), (-346819134916025868541420729/2998487451475600000000000)]
    bernstein := [(136246441847856924563076799/468513664293062500000000000), (2310367049381714429525128261/7496218628689000000000000000), (28154514575963423602974382753/89954623544268000000000000000), (292980077649934007469982920953/959515984472192000000000000000), (2190905933801913779741503162471/7676127875777536000000000000000)]
    reserve := (57083622609/200000000000) }

theorem quarter_037_007_valid : quarter_037_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_037_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_037_007]
  · intro i; fin_cases i <;> norm_num [quarter_037_007]
  · norm_num [quarter_037_007]
  · norm_num [quarter_037_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_037_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_037_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_037_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_037_007]

def quarter_037_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 3, 0, 0, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (24049023/100000000), (75950977/100000000)]
    cone := fun i => (![![0, 0, (18645369/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(187883/1562500), 0, (24049023/100000000), 0, 0], ![0, 0, (72043011/100000000), 0, 0]] i.1) i.2
    mu := ![(1727587/10000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (468331/100000000)]
    alternative := .zero
    polynomial := [(-592130163232521009777523/202270636824250000000000), (-1826546792745471/46833100000000), (-12408257453348347240388773/101135318412125000000000), (-1826546792745471/46833100000000), (-24224384743464173471000023/202270636824250000000000)]
    bernstein := [(122784263339620107957711558377/517812830270080000000000000000), (66124220278493264215192924433/258906415135040000000000000000), (101259237814788241533305556971/388359622702560000000000000000), (104431986989384370034921429/412271361680000000000000000), (7548604663746480273710102537/32363301891880000000000000000)]
    reserve := (5831145327/25000000000) }

theorem quarter_037_008_valid : quarter_037_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_037_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_037_008]
  · intro i; fin_cases i <;> norm_num [quarter_037_008]
  · norm_num [quarter_037_008]
  · norm_num [quarter_037_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_037_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_037_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_037_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_037_008]

def quarter_037_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 3, 0, 0, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (664171/3125000), (2460829/3125000)]
    cone := fun i => (![![0, 0, (3866331/10000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(664171/6250000), 0, (664171/3125000), 0, 0], ![0, 0, (4739011/6250000), 0, 0]] i.1) i.2
    mu := ![(4477937/25000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (489/100000)]
    alternative := .zero
    polynomial := [(-4733832133543288874689/2189711193000000000000), (-1634411257759/47753906250), (-46140063934181650534123/364951865500000000000), (-1634411257759/47753906250), (-272106551471546614330049/2189711193000000000000)]
    bernstein := [(63056820484380790782766031/350353790880000000000000000), (9303894629255031036217799/46713838784000000000000000), (3831329916890693390789357/18685535513600000000000000), (295623248417801293123283/1494842841088000000000000), (63657156070695807467159/358762281861120000000000)]
    reserve := (44358868873/250000000000) }

theorem quarter_037_009_valid : quarter_037_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_037_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_037_009]
  · intro i; fin_cases i <;> norm_num [quarter_037_009]
  · norm_num [quarter_037_009]
  · norm_num [quarter_037_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_037_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_037_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_037_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_037_009]

def quarter_037_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 3, 0, 0, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (18179523/100000000), (81820477/100000000)]
    cone := fun i => (![![0, 0, (40172571/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(9089761/100000000), 0, (18179523/100000000), 0, 0], ![0, 0, (79775281/100000000), 0, 0]] i.1) i.2
    mu := ![(18610951/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (511071/100000000)]
    alternative := .zero
    polynomial := [(-9525812173751588768646093/6341011559014000000000000), (-495819081164157/17035700000000), (-1243361023064464170147808279/9511517338521000000000000), (-495819081164157/17035700000000), (-144596741741627857293510487/1119002039826000000000000)]
    bernstein := [(369664029148369400685842849/3116734001486561280000000000), (2702541507450695926369574213/19479587509291008000000000000), (53006201815115764320021341327/365242265799206400000000000000), (20988043749633593264040589501/152184277416336000000000000000), (22291761804267451665470075921/190230346770420000000000000000)]
    reserve := (29295748789/250000000000) }

theorem quarter_037_010_valid : quarter_037_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_037_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_037_010]
  · intro i; fin_cases i <;> norm_num [quarter_037_010]
  · norm_num [quarter_037_010]
  · norm_num [quarter_037_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_037_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_037_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_037_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_037_010]

def quarter_037_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 1]
    lambda := ![(502719/10000000), (458931/4000000), (1568309/12500000), (1568309/12500000), (470533/6250000), (470533/6250000), (8669907/20000000)]
    cone := fun i => (![![0, 0, (2186361/12500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (42690789/100000000), 0, 0]] i.1) i.2
    mu := ![(163001/1562500), (3165151/100000000), (330729/50000000), (1/100000000), (369719/10000000), (1/100000000), (272033/100000000)]
    alternative := .zero
    polynomial := [(-2438166319476972819946101216577798429261/5603691829212397662615798672000000000000), (-33260040687063/2720330000000), (-1394006067488291108812789682158221256604827/19612921402243391819155295352000000000000), (-33260040687063/2720330000000), (-2770944970740243407885956655800397924204827/39225842804486783638310590704000000000000)]
    bernstein := [(32145835329334888301887393048433846450559773/392258428044867836383105907040000000000000000), (147259515500781408884186001413077187278926619/1569033712179471345532423628160000000000000000), (1850708740037170741311099037890403422650272571/18828404546153656146389083537920000000000000000), (2393283637911424865584452744075375459136642871/25104539394871541528518778050560000000000000000), (8536189704312903153056632477405992675515271413/100418157579486166114075112202240000000000000000)]
    reserve := (16390131113/200000000000) }

theorem quarter_037_011_valid : quarter_037_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_037_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_037_011]
  · intro i; fin_cases i <;> norm_num [quarter_037_011]
  · norm_num [quarter_037_011]
  · norm_num [quarter_037_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_037_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_037_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_037_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_037_011]

def quarter_037_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 3, 0, 0, 0, 0, 1]
    lambda := ![(1995647/25000000), (1930617/10000000), (10290131/50000000), (10290131/50000000), (10087721/100000000), (10087721/100000000), (11375277/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6775657/50000000), 0, 0]] i.1) i.2
    mu := ![(1755711/50000000), (1055767/20000000), (819289/100000000), (1/100000000), (1447833/25000000), (1/100000000), (116577/5000000)]
    alternative := .zero
    polynomial := [(96492742848042741000336862128599494499/1898697658637118137543407243800000000000), (-68258945292439/77718000000000), (-5135174282458054899727708105182535663801/949348829318559068771703621900000000000), (-68258945292439/77718000000000), (-10366841307764152540455753072493670822101/1898697658637118137543407243800000000000)]
    bernstein := [(420270294431127095817705069692811839088073019/4860666006111022432111122544128000000000000000), (209033532940165321811491116765387450038570773/2430333003055511216055561272064000000000000000), (309848874431214980616224556633047772674583473/3645499504583266824083341908096000000000000000), (50684877370812715066282824023103445809306197/607583250763877804013890318016000000000000000), (24694542666573421982058582772008959503175099/303791625381938902006945159008000000000000000)]
    reserve := (81287766361/1000000000000) }

theorem quarter_037_012_valid : quarter_037_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_037_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_037_012]
  · intro i; fin_cases i <;> norm_num [quarter_037_012]
  · norm_num [quarter_037_012]
  · norm_num [quarter_037_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_037_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_037_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_037_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_037_012]

def quarter_037_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 1]
    lambda := ![(6995241/100000000), (20567447/100000000), (1339171/6250000), (1339171/6250000), (10538289/100000000), (10538289/100000000), (8507263/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1383637/12500000), 0, 0]] i.1) i.2
    mu := ![(2783003/100000000), (5489343/100000000), (572549/100000000), (1/100000000), (3016751/50000000), (1/100000000), (329597/12500000)]
    alternative := .zero
    polynomial := [(265814430925558078331998761050069928811/4045115801606044174256781828180000000000), (-198115497354751/263677600000000), (-16024214854338990136031781023111083659089/2022557900803022087128390914090000000000), (-198115497354751/263677600000000), (-32314244139603538350395560807272237246989/4045115801606044174256781828180000000000)]
    bernstein := [(54053954793007845600015671093358825270815311/647218528256967067881085092508800000000000000), (6023649088708217695340517009576288644890727/71913169806329674209009454723200000000000000), (646045296516758373618341386531211843905496983/7766622339083604814573021110105600000000000000), (11761976274159410439792590347847377960536751/143826339612659348418018909446400000000000000), (823813078987511477091071592391743884277375211/10355496452111473086097361480140800000000000000)]
    reserve := (79553219181/1000000000000) }

theorem quarter_037_013_valid : quarter_037_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_037_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_037_013]
  · intro i; fin_cases i <;> norm_num [quarter_037_013]
  · norm_num [quarter_037_013]
  · norm_num [quarter_037_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_037_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_037_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_037_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_037_013]

def quarter_037_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 3, 0, 0, 0, 0, 1]
    lambda := ![0, (2490497/10000000), (12631003/50000000), (12631003/50000000), (12285509/100000000), (12285509/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (3688527/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (100263/3125000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3236973/50000000), (329393/100000000), (1/100000000), (7098027/100000000), (1/100000000), (100263/3125000)]
    alternative := .zero
    polynomial := [(580001460087322363593610597592611/7099955994483341250014400000000000), (-2490497/5000000), (-67225534405836510641900943231687389/3549977997241670625007200000000000), (-2490497/5000000), (-135031070271760343647395497060967389/7099955994483341250014400000000000)]
    bernstein := [(1496023420543659356169532861310917947811/18175887345877353600036864000000000000000), (966893419384116429679115113248736211/11359929591173346000023040000000000000), (2928970503266024169805075283094445411/34079788773520038000069120000000000000), (602104483967813336010031989038611/7099955994483341250014400000000000), (580001460087322363593610597592611/7099955994483341250014400000000000)]
    reserve := (81690852807/1000000000000) }

theorem quarter_037_014_valid : quarter_037_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_037_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_037_014]
  · intro i; fin_cases i <;> norm_num [quarter_037_014]
  · norm_num [quarter_037_014]
  · norm_num [quarter_037_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_037_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_037_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_037_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_037_014]

def quarter_037_015 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 1]
    lambda := ![0, (5074861/20000000), (3170797/12500000), (3170797/12500000), (11946471/100000000), (11946471/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (3758037/50000000), 0, 0], ![(634259/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1559937/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (6595947/100000000), (80139/50000000), (1/100000000), (708483/10000000), (1/100000000), (24959/800000)]
    alternative := .zero
    polynomial := [(178860867827494066751767836068651/2077137169420931028378000000000000), (3218776262999/3205560000000), (-41528609366120494694388801437331349/1038568584710465514189000000000000), (3218776262999/3205560000000), (-83236079600068483455529370710731349/2077137169420931028378000000000000)]
    bernstein := [(178860867827494066751767836068651/2077137169420931028378000000000000), (383792998616549549887622480917927/4154274338841862056756000000000000), (942145618421345824357713493839193451/9970258413220468936214400000000000000), (614465691794196384276880241500801127/6646838942146979290809600000000000000), (458477329991870607797979505110473511851/5317471153717583432647680000000000000000)]
    reserve := (10763664917/125000000000) }

theorem quarter_037_015_valid : quarter_037_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_037_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_037_015]
  · intro i; fin_cases i <;> norm_num [quarter_037_015]
  · norm_num [quarter_037_015]
  · norm_num [quarter_037_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_037_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_037_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_037_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_037_015]

def quarter_037_016 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 3, 0, 0, 0, 0, 1]
    lambda := ![0, (25647901/100000000), (6393967/25000000), (6393967/25000000), (5800091/50000000), (5800091/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (1899279/25000000), 0, 0], ![(1920891/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3029439/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1666767/25000000), (80927/50000000), (1/100000000), (7096167/100000000), (1/100000000), (9467/312500)]
    alternative := .zero
    polynomial := [(178902874849751607836628769291927/3717576505974544711344000000000000), (7038117457113/2312200000000), (-75154692105168230483270770948948073/1858788252987272355672000000000000), (7038117457113/2312200000000), (-150488287085186212574378170667188073/3717576505974544711344000000000000)]
    bernstein := [(942019308851389465500816889488022498327/9516995855294834461040640000000000000000), (55723110848077815874407094661095066303/528721991960824136724480000000000000000), (768004507455517765324237100306226696181/7137746891471125845780480000000000000000), (13957667001283332803188972267082862703/132180497990206034181120000000000000000), (59104138790536613498027922400637873527/594812240955927153815040000000000000000)]
    reserve := (98982843239/1000000000000) }

theorem quarter_037_016_valid : quarter_037_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_037_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_037_016]
  · intro i; fin_cases i <;> norm_num [quarter_037_016]
  · norm_num [quarter_037_016]
  · norm_num [quarter_037_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_037_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_037_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_037_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_037_016]

def quarter_037_017 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 1]
    lambda := ![0, (649029/2500000), (3219891/12500000), (3219891/12500000), (2815073/25000000), (2815073/25000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (3844953/50000000), 0, 0], ![(1616259/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (735169/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3374249/50000000), (81737/50000000), (1/100000000), (710353/10000000), (1/100000000), (735169/25000000)]
    alternative := .zero
    polynomial := [(-12359044121777524290999325450264727/288062829319027892638082000000000000), (1048998962511/204342500000), (-5904373284900318057681999894293464727/144031414659513946319041000000000000), (1048998962511/204342500000), (-11796387525678858591073000463136664727/288062829319027892638082000000000000)]
    bernstein := [(5147073797592613867379520881263303233673/46090052691044462822093120000000000000000), (10900343662169963596141591874975159911819/92180105382088925644186240000000000000000), (3509813857863707656917423040811580855409/29109506962764923887637760000000000000000), (43740990546166461978796767902445534768371/368720421528355702576744960000000000000000), (82882238014479466318793373914733116899513/737440843056711405153489920000000000000000)]
    reserve := (111674287553/1000000000000) }

theorem quarter_037_017_valid : quarter_037_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_037_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_037_017]
  · intro i; fin_cases i <;> norm_num [quarter_037_017]
  · norm_num [quarter_037_017]
  · norm_num [quarter_037_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_037_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_037_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_037_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_037_017]

def quarter_037_018 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 3, 0, 0, 0, 0, 1]
    lambda := ![0, (26315417/100000000), (6478881/25000000), (6478881/25000000), (10926767/100000000), (10926767/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (194871/2500000), 0, 0], ![(4570207/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1426787/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3420293/50000000), (82569/50000000), (1/100000000), (3553297/50000000), (1/100000000), (114143/4000000)]
    alternative := .zero
    polynomial := [(-43357332535523216896953959891393489/229082083387306584585414000000000000), (120266902981319/16513800000000), (-4773610212565416681368891982094013489/114541041693653292292707000000000000), (120266902981319/16513800000000), (-9503863092595310145840830004296633489/229082083387306584585414000000000000)]
    bernstein := [(4287219611667127532259722659138542821423/34497066674794403325803520000000000000000), (6404753847585274717802413139601354834399/48870844455958738044888320000000000000000), (14681250081700145968414633271518472256097/109959400025907160600998720000000000000000), (1206246378452444183952503965366609622233/9163283335492263383416560000000000000000), (287246162859689309369247871526431478711/2290820833873065845854140000000000000000)]
    reserve := (62138900853/500000000000) }

theorem quarter_037_018_valid : quarter_037_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_037_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_037_018]
  · intro i; fin_cases i <;> norm_num [quarter_037_018]
  · norm_num [quarter_037_018]
  · norm_num [quarter_037_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_037_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_037_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_037_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_037_018]

def quarter_037_019 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 3, 0, 0, 0, 0, 1]
    lambda := ![0, (3339007/12500000), (26044357/100000000), (26044357/100000000), (2119923/20000000), (2119923/20000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (7912327/100000000), 0, 0], ![(741887/12500000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2768137/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (694369/10000000), (3337/2000000), (1/100000000), (7105029/100000000), (1/100000000), (2768137/100000000)]
    alternative := .zero
    polynomial := [(-4950243528964749860285420081748157/12571640533456372242888000000000000), (2477165886209/260703125000), (-267044017347080972000205918769408957/6285820266728186121444000000000000), (2477165886209/260703125000), (-529137791165197194140126417457069757/12571640533456372242888000000000000)]
    bernstein := [(17208194324370500429757934362887216843/125716405334563722428880000000000000000), (4823910042873540428021058846652615861/33524374755883659314368000000000000000), (35364571328600819959719954834447098741/241375498242362347063449600000000000000), (47767624042506748464679960523672081/330086151442546799403008000000000000), (21935773506468223359202044969865319/158441352692422463713443840000000000)]
    reserve := (34220264011/250000000000) }

theorem quarter_037_019_valid : quarter_037_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_037_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_037_019]
  · intro i; fin_cases i <;> norm_num [quarter_037_019]
  · norm_num [quarter_037_019]
  · norm_num [quarter_037_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_037_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_037_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_037_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_037_019]

def quarter_037_020 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 3, 0, 0, 0, 0, 1]
    lambda := ![0, (27152517/100000000), (26144863/100000000), (26144863/100000000), (5139439/50000000), (5139439/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (1608559/20000000), 0, 0], ![(732839/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (859/32000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3529093/50000000), (42153/25000000), (1/100000000), (3549253/50000000), (1/100000000), (859/32000)]
    alternative := .zero
    polynomial := [(-11968884148465608750907315942646171/18141855562390413835320000000000000), (6632807801921/562040000000), (-393877709322117776695978700306696171/9070927781195206917660000000000000), (6632807801921/562040000000), (-775786534495769944641050084670746171/18141855562390413835320000000000000)]
    bernstein := [(444563730642749187053163246534137101/2972361615342045402778828800000000000), (5827559100083240791414905989792983651/37154520191775567534735360000000000000), (222436093456270458588264529331965809367/1393294507191583782552576000000000000000), (183370826384954401604153423593534017943/1161078755992986485460480000000000000000), (440176559557960292402240942522289768949/2902696889982466213651200000000000000000)]
    reserve := (149565829523/1000000000000) }

theorem quarter_037_020_valid : quarter_037_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_037_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_037_020]
  · intro i; fin_cases i <;> norm_num [quarter_037_020]
  · norm_num [quarter_037_020]
  · norm_num [quarter_037_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_037_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_037_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_037_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_037_020]

def quarter_037_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 1]
    lambda := ![0, (27638311/100000000), (5243243/20000000), (5243243/20000000), (9964629/100000000), (9964629/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2046673/25000000), 0, 0], ![(8751361/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (650577/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (7184467/100000000), (6817/4000000), (1/100000000), (7086689/100000000), (1/100000000), (650577/25000000)]
    alternative := .zero
    polynomial := [(-149197832755212289691105001426534931/150535409694329028181378000000000000), (14227813940663/1002500000000), (-3349248539319842894971164876516416931/75267704847164514090689000000000000), (14227813940663/1002500000000), (-6549299245884473500251224751606298931/150535409694329028181378000000000000)]
    bernstein := [(3911714617723147752327811313504524347389/24085665551092644509020480000000000000000), (8188817838107347949360460357094262262441/48171331102185289018040960000000000000000), (16666996176781981227796259722082055547029/96342662204370578036081920000000000000000), (1942406722990930358064771619355017531953/11334430847573009180715520000000000000000), (3741623160036345005793423887559143985757/22668861695146018361431040000000000000000)]
    reserve := (40602102207/250000000000) }

theorem quarter_037_021_valid : quarter_037_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_037_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_037_021]
  · intro i; fin_cases i <;> norm_num [quarter_037_021]
  · norm_num [quarter_037_021]
  · norm_num [quarter_037_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_037_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_037_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_037_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_037_021]

def quarter_037_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 3, 0, 0, 0, 0, 1]
    lambda := ![0, (7042757/25000000), (6564381/25000000), (6564381/25000000), (4828481/50000000), (4828481/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (8344487/100000000), 0, 0], ![(10205353/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2521959/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (114421/1562500), (17229/10000000), (1/100000000), (7069237/100000000), (1/100000000), (2521959/100000000)]
    alternative := .zero
    polynomial := [(-4176066171567778551238924072300817237/2999128572668356487487744000000000000), (71873821278221/4307250000000), (-68557624456686465845509369193584913237/1499564286334178243743872000000000000), (71873821278221/4307250000000), (-132939182741805153139779814314869009237/2999128572668356487487744000000000000)]
    bernstein := [(449098003270324706130405189134104467940121/2559256382010330869322874880000000000000000), (58672782727191301356126074211729225444903/319907047751291358665359360000000000000000), (16792123314567444578048809677493304895109/89973857180050694624632320000000000000000), (462632520676601837909225118723630234411/2499273810556963739573120000000000000000), (83765958852063035089801970282517918947/468613839479430701169960000000000000000)]
    reserve := (87739940091/500000000000) }

theorem quarter_037_022_valid : quarter_037_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_037_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_037_022]
  · intro i; fin_cases i <;> norm_num [quarter_037_022]
  · norm_num [quarter_037_022]
  · norm_num [quarter_037_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_037_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_037_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_037_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_037_022]

def quarter_037_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 1]
    lambda := ![0, (14376173/50000000), (26267841/100000000), (26267841/100000000), (4677993/50000000), (4677993/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (4258339/50000000), 0, 0], ![(1169179/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1221679/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1494811/20000000), (43553/25000000), (1/100000000), (1761451/25000000), (1/100000000), (1221679/50000000)]
    alternative := .zero
    polynomial := [(-2111437502601256375680995594262421/1129822840859748931174250000000000), (16808319571967/871060000000), (-13301033632489091720687278687992773/282455710214937232793562500000000), (16808319571967/871060000000), (-51092697027355110507068119157708671/1129822840859748931174250000000000)]
    bernstein := [(4167244087126120477453416961761747/22066852360541971311997070312500000), (1113722960395961669093738574808722411/5649114204298744655871250000000000000), (877430192922085339554844563273754637/4373507771069995862610000000000000000), (9002520720337188515726880338362163827/45192913634389957246970000000000000000), (557646812097592912645153404627525626369/2892346472600957263806080000000000000000)]
    reserve := (188846330189/1000000000000) }

theorem quarter_037_023_valid : quarter_037_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_037_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_037_023]
  · intro i; fin_cases i <;> norm_num [quarter_037_023]
  · norm_num [quarter_037_023]
  · norm_num [quarter_037_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_037_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_037_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_037_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_037_023]

def quarter_037_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 3, 0, 0, 0, 0, 1]
    lambda := ![0, (29384049/100000000), (13123079/50000000), (13123079/50000000), (9061817/100000000), (9061817/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (8703793/100000000), 0, 0], ![(6606087/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1183267/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (954783/12500000), (176191/100000000), (1/100000000), (3508017/50000000), (1/100000000), (473307/20000000)]
    alternative := .zero
    polynomial := [(-2409475476006741540488196045645642557/993117155095368866403936000000000000), (194113584106263/8809550000000), (-24144700775510029205831275066817802557/496558577547684433201968000000000000), (194113584106263/8809550000000), (-45879926075013316871174354087989962557/993117155095368866403936000000000000)]
    bernstein := [(515007188540992121631011941927568240569123/2542379917044144297994076160000000000000000), (53717684629651122274081053949269729384427/254237991704414429799407616000000000000000), (16400758753422607986450126234157567147657/76271397511324328939822284800000000000000), (543358433556511060161422944722747973739/2542379917044144297994076160000000000000), (52693630026050039937102557374861141027/254237991704414429799407616000000000000)]
    reserve := (25321116697/125000000000) }

theorem quarter_037_024_valid : quarter_037_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_037_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_037_024]
  · intro i; fin_cases i <;> norm_num [quarter_037_024]
  · norm_num [quarter_037_024]
  · norm_num [quarter_037_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_037_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_037_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_037_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_037_024]

def quarter_037_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 1]
    lambda := ![0, (30068033/100000000), (13095703/50000000), (13095703/50000000), (8774577/100000000), (8774577/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (1781279/20000000), 0, 0], ![(14768103/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (7161/312500), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (7816063/100000000), (178231/100000000), (1/100000000), (1744891/25000000), (1/100000000), (2291521/100000000)]
    alternative := .zero
    polynomial := [(-68424235846996335557360886771754168019/22280422937930644315750732000000000000), (444047808351399/17823100000000), (-560660971569508818655208787559286448019/11140211468965322157875366000000000000), (444047808351399/17823100000000), (-1052897707292021301753056688346818728019/22280422937930644315750732000000000000)]
    bernstein := [(1236032995940810521941481486859974962509/5703788272110244944832187392000000000000), (12883724901643286091877925247286517048767/57037882721102449448321873920000000000000), (393414916605567701802077876324151232500959/1711136481633073483449656217600000000000000), (1304566892122243340743061172262342310440471/5703788272110244944832187392000000000000000), (12673209113233940396102004689521417668677021/57037882721102449448321873920000000000000000)]
    reserve := (216703870651/1000000000000) }

theorem quarter_037_025_valid : quarter_037_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_037_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_037_025]
  · intro i; fin_cases i <;> norm_num [quarter_037_025]
  · norm_num [quarter_037_025]
  · norm_num [quarter_037_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_037_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_037_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_037_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_037_025]

def quarter_037_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 3, 0, 0, 0, 0, 1]
    lambda := ![0, (1232253/4000000), (26102459/100000000), (26102459/100000000), (8494379/100000000), (8494379/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (9125083/100000000), 0, 0], ![(654451/4000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (443669/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (8007979/100000000), (180333/100000000), (1/100000000), (3468011/50000000), (1/100000000), (1109173/50000000)]
    alternative := .zero
    polynomial := [(-84675452296940722030186774774525837057/22219684093204284380341284000000000000), (29868489189/1068640000), (-580073159097390875407396868685375337057/11109842046602142190170642000000000000), (29868489189/1068640000), (-1075470865897841028784606962596224837057/22219684093204284380341284000000000000)]
    bernstein := [(13157023327929315511047832402560239786258063/56882391278602968013673687040000000000000000), (3426825758913662941727991527780389211482999/14220597819650742003418421760000000000000000), (2616507611252953664588122731943498316354681/10665448364738056502563816320000000000000000), (217087753491234622954055383620682602920771/888787363728171375213651360000000000000000), (52802088583925546581990227420571060925783/222196840932042843803412840000000000000000)]
    reserve := (46260443811/200000000000) }

theorem quarter_037_026_valid : quarter_037_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_037_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_037_026]
  · intro i; fin_cases i <;> norm_num [quarter_037_026]
  · norm_num [quarter_037_026]
  · norm_num [quarter_037_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_037_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_037_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_037_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_037_026]

def quarter_037_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 1]
    lambda := ![0, (31601097/100000000), (12989063/50000000), (12989063/50000000), (328853/4000000), (328853/4000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (9360501/100000000), 0, 0], ![(17993507/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (536759/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (8214577/100000000), (91251/50000000), (1/100000000), (6885023/100000000), (1/100000000), (536759/25000000)]
    alternative := .zero
    polynomial := [(-51566053001737589024376888553120711801/11080709243565573515211756000000000000), (63179395564131/2027800000000), (-300784343828634786869279466058030291801/5540354621782786757605878000000000000), (63179395564131/2027800000000), (-550002634655531984714182043562939871801/11080709243565573515211756000000000000)]
    bernstein := [(27303917439014261505922441449866874532319/110807092435655735152117560000000000000000), (113743187619235838942353037678637385900349/443228369742622940608470240000000000000000), (198550806538804108721670660071421810891191/759820062415925041043091840000000000000000), (1846413379195097361009488033840911098739609/7091653915881967049735523840000000000000000), (7195136565931505714239099137977779910550839/28366615663527868198942095360000000000000000)]
    reserve := (24640947469/100000000000) }

theorem quarter_037_027_valid : quarter_037_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_037_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_037_027]
  · intro i; fin_cases i <;> norm_num [quarter_037_027]
  · norm_num [quarter_037_027]
  · norm_num [quarter_037_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_037_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_037_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_037_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_037_027]

def quarter_037_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 3, 0, 0, 0, 0, 1]
    lambda := ![0, (32454687/100000000), (25817159/100000000), (25817159/100000000), (7955497/100000000), (7955497/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (9613341/100000000), 0, 0], ![(4916687/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1038807/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (527279/6250000), (9237/5000000), (1/100000000), (106659/1562500), (1/100000000), (1038807/50000000)]
    alternative := .zero
    polynomial := [(-93173425690335524545312937833063/16612281367291358784000000000000), (53189845887323/1539500000000), (-469898231631983458912512163897063/8306140683645679392000000000000), (53189845887323/1539500000000), (-846623037573631393279711389961063/16612281367291358784000000000000)]
    bernstein := [(11144966957699935585774071315931209257/42527440300265878487040000000000000000), (644683219982000528299987220892275747/2362635572236993249280000000000000000), (8864374305585048555808222957055768291/31895580225199408865280000000000000000), (163670885524730980456734444899028587/590658893059248312320000000000000000), (718349927775541421594091584462298137/2657965018766617405440000000000000000)]
    reserve := (262065313101/1000000000000) }

theorem quarter_037_028_valid : quarter_037_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_037_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_037_028]
  · intro i; fin_cases i <;> norm_num [quarter_037_028]
  · norm_num [quarter_037_028]
  · norm_num [quarter_037_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_037_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_037_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_037_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_037_028]

def quarter_037_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 3, 0, 0, 0, 0, 1]
    lambda := ![0, (19720573/50000000), (30279427/100000000), (30279427/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (11682787/100000000), 0, 0], ![(6318427/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8969011/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2050513/20000000), (44217/20000000), (1/100000000), (3935507/50000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-22680415425699938123471916482143/2854581696460229976000000000000), (124603000898671/2763562500000), (-33259901940493286369482729819381/475763616076704996000000000000), (124603000898671/2763562500000), (-10404646836309398829024968378479/167916570380013528000000000000)]
    bernstein := [(125595674631704441966965824124417057/456733071433636796160000000000000000), (52630386664879708104060371205200533/182693228573454718464000000000000000), (21490539329017527592283827192235081/73077291429381887385600000000000000), (8559427822631408010058551107844541/29230916571752754954240000000000000), (3322013469597050272138188119811953/11692366628701101981696000000000000)]
    reserve := (274987038353/1000000000000) }

theorem quarter_037_029_valid : quarter_037_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_037_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_037_029]
  · intro i; fin_cases i <;> norm_num [quarter_037_029]
  · norm_num [quarter_037_029]
  · norm_num [quarter_037_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_037_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_037_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_037_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_037_029]

def quarterTable037 : OwnerTable where
  mode := .quarter
  owners := ![0, 3, 0, 0, 0, 0, 1]
  rows := [quarter_037_000, quarter_037_001, quarter_037_002, quarter_037_003, quarter_037_004, quarter_037_005, quarter_037_006, quarter_037_007, quarter_037_008, quarter_037_009, quarter_037_010, quarter_037_011, quarter_037_012, quarter_037_013, quarter_037_014, quarter_037_015, quarter_037_016, quarter_037_017, quarter_037_018, quarter_037_019, quarter_037_020, quarter_037_021, quarter_037_022, quarter_037_023, quarter_037_024, quarter_037_025, quarter_037_026, quarter_037_027, quarter_037_028, quarter_037_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_037_000_valid
    · exact quarter_037_001_valid
    · exact quarter_037_002_valid
    · exact quarter_037_003_valid
    · exact quarter_037_004_valid
    · exact quarter_037_005_valid
    · exact quarter_037_006_valid
    · exact quarter_037_007_valid
    · exact quarter_037_008_valid
    · exact quarter_037_009_valid
    · exact quarter_037_010_valid
    · exact quarter_037_011_valid
    · exact quarter_037_012_valid
    · exact quarter_037_013_valid
    · exact quarter_037_014_valid
    · exact quarter_037_015_valid
    · exact quarter_037_016_valid
    · exact quarter_037_017_valid
    · exact quarter_037_018_valid
    · exact quarter_037_019_valid
    · exact quarter_037_020_valid
    · exact quarter_037_021_valid
    · exact quarter_037_022_valid
    · exact quarter_037_023_valid
    · exact quarter_037_024_valid
    · exact quarter_037_025_valid
    · exact quarter_037_026_valid
    · exact quarter_037_027_valid
    · exact quarter_037_028_valid
    · exact quarter_037_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
