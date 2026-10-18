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

def quarter_025_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 2, 0, 0, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (305109/781250), (476141/781250)]
    cone := fun i => (![![0, 0, (14961777/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(305109/1562500), 0, (305109/781250), 0, 0], ![0, 0, (46788991/100000000), 0, 0]] i.1) i.2
    mu := ![(13862837/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (341629/100000000)]
    alternative := .zero
    polynomial := [(-14374691271790946411340937/1183986785368250000000000), (-9297593879616/133448828125), (-63788844655569788786860937/591993392684125000000000), (-9297593879616/133448828125), (-113202998039348631162380937/1183986785368250000000000)]
    bernstein := [(2990005041502588170728626727/4849609872868352000000000000), (7620368667567275881374279419/12124024682170880000000000000), (57200606057925900106726513837/90930185116281600000000000000), (46860259961119773118474510947/75775154263568000000000000000), (113063918489006412728021519863/189437885658920000000000000000)]
    reserve := (14920975033/25000000000) }

theorem quarter_025_000_valid : quarter_025_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_025_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_025_000]
  · intro i; fin_cases i <;> norm_num [quarter_025_000]
  · norm_num [quarter_025_000]
  · norm_num [quarter_025_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_025_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_025_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_025_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_025_000]

def quarter_025_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (37732553/100000000), (62267447/100000000)]
    cone := fun i => (![![0, 0, (1528617/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(18866277/100000000), 0, (37732553/100000000), 0, 0], ![0, 0, (4953271/10000000), 0, 0]] i.1) i.2
    mu := ![(14163403/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (354441/100000000)]
    alternative := .zero
    polynomial := [(-107611658598710606406360499/10040181445446000000000000), (-2349509744102191/35444100000000), (-181483337459563315242486833/1673363574241000000000000), (-2349509744102191/35444100000000), (-981288366158669285048560499/10040181445446000000000000)]
    bernstein := [(919532253676100215105530441101/1606429031271360000000000000000), (1879851632914358466935883430559/3212858062542720000000000000000), (3767188926728837572299399960181/6425716125085440000000000000000), (7404713308036821615973784746679/12851432250170880000000000000000), (14266927128878180023579413088861/25702864500341760000000000000000)]
    reserve := (277535741759/500000000000) }

theorem quarter_025_001_valid : quarter_025_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_025_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_025_001]
  · intro i; fin_cases i <;> norm_num [quarter_025_001]
  · norm_num [quarter_025_001]
  · norm_num [quarter_025_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_025_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_025_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_025_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_025_001]

def quarter_025_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 2, 0, 0, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (36281179/100000000), (63718821/100000000)]
    cone := fun i => (![![0, 0, (15642471/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1814059/10000000), 0, (36281179/100000000), 0, 0], ![0, 0, (6547619/12500000), 0, 0]] i.1) i.2
    mu := ![(7246767/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (367987/100000000)]
    alternative := .zero
    polynomial := [(-8328927597030419362173933/888905349343000000000000), (-2311793950369959/36798700000000), (-48640910973048999170613933/444452674671500000000000), (-2311793950369959/36798700000000), (-88952894349067578979053933/888905349343000000000000)]
    bernstein := [(1201621007407386091306135973187/2275597694318080000000000000000), (308040043995528656192395392597/568899423579520000000000000000), (77265236295115823350674097207/142224855894880000000000000000), (18976090232022837413552977017/35556213973720000000000000000), (4559949838646291704679922027/8889053493430000000000000000)]
    reserve := (128246214347/250000000000) }

theorem quarter_025_002_valid : quarter_025_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_025_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_025_002]
  · intro i; fin_cases i <;> norm_num [quarter_025_002]
  · norm_num [quarter_025_002]
  · norm_num [quarter_025_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_025_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_025_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_025_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_025_002]

def quarter_025_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (34687529/100000000), (65312471/100000000)]
    cone := fun i => (![![0, 0, (32067399/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(3468753/20000000), 0, (34687529/100000000), 0, 0], ![0, 0, (27669903/50000000), 0, 0]] i.1) i.2
    mu := ![(14856027/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (95581/25000000)]
    alternative := .zero
    polynomial := [(-22993938576098725413408389/2839907833374000000000000), (-2265528231874159/38232400000000), (-157232236230409305195663389/1419953916687000000000000), (-2265528231874159/38232400000000), (-291470533884719884977918389/2839907833374000000000000)]
    bernstein := [(13721315095064621478401170291/28399078333740000000000000000), (56494547290367897220467356867/113596313334960000000000000000), (681225850798745907422906180437/1363155760019520000000000000000), (891783001585839687797971583423/1817541013359360000000000000000), (3418956771277319837318513405851/7270164053437440000000000000000)]
    reserve := (470272300067/1000000000000) }

theorem quarter_025_003_valid : quarter_025_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_025_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_025_003]
  · intro i; fin_cases i <;> norm_num [quarter_025_003]
  · norm_num [quarter_025_003]
  · norm_num [quarter_025_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_025_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_025_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_025_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_025_003]

def quarter_025_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 2, 0, 0, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (32937947/100000000), (67062053/100000000)]
    cone := fun i => (![![0, 0, (2057901/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(8234487/50000000), 0, (32937947/100000000), 0, 0], ![0, 0, (29207921/50000000), 0, 0]] i.1) i.2
    mu := ![(3813497/25000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (79503/20000000)]
    alternative := .zero
    polynomial := [(-522976290930603728141567/75796112997750000000000), (-2208886347425191/39751500000000), (-1419268948894550494390689/12632685499625000000000), (-2208886347425191/39751500000000), (-7992637402436699238202567/75796112997750000000000)]
    bernstein := [(84874092072739102667061094153/194038049274240000000000000000), (8777224093450606029420858503/19403804927424000000000000000), (294530147709546860396101443/646793497580800000000000000), (86680303311943665214532231/194038049274240000000000000), (8277382639847301395568137/19403804927424000000000000)]
    reserve := (426585541897/1000000000000) }

theorem quarter_025_004_valid : quarter_025_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_025_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_025_004]
  · intro i; fin_cases i <;> norm_num [quarter_025_004]
  · norm_num [quarter_025_004]
  · norm_num [quarter_025_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_025_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_025_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_025_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_025_004]

def quarter_025_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (31017243/100000000), (68982757/100000000)]
    cone := fun i => (![![0, 0, (8467363/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7754311/50000000), 0, (31017243/100000000), 0, 0], ![0, 0, (30808081/50000000), 0, 0]] i.1) i.2
    mu := ![(15690873/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (41363/10000000)]
    alternative := .zero
    polynomial := [(-3751957175530520117015977/649021579899000000000000), (-2139654936678951/41363000000000), (-5299802024152296461536711/46358684278500000000000), (-2139654936678951/41363000000000), (-70445271162601630344497977/649021579899000000000000)]
    bernstein := [(64865702008638222482352647/166149524454144000000000000), (674792094324244282489899079/1661495244541440000000000000), (20424339739921842881447883077/49844857336243200000000000000), (9529763332552959388327432721/23735646350592000000000000000), (633906697069892355947829894503/1661495244541440000000000000000)]
    reserve := (381527843159/1000000000000) }

theorem quarter_025_005_valid : quarter_025_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_025_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_025_005]
  · intro i; fin_cases i <;> norm_num [quarter_025_005]
  · norm_num [quarter_025_005]
  · norm_num [quarter_025_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_025_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_025_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_025_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_025_005]

def quarter_025_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 2, 0, 0, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (7227123/25000000), (17772877/25000000)]
    cone := fun i => (![![0, 0, (6980963/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7227123/50000000), 0, (7227123/25000000), 0, 0], ![0, 0, (32474227/50000000), 0, 0]] i.1) i.2
    mu := ![(16170531/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (430747/100000000)]
    alternative := .zero
    polynomial := [(-1270666289333411194334611/267900296794500000000000), (-128446768142871/2692168750000), (-15629113707204217875794611/133950148397250000000000), (-128446768142871/2692168750000), (-29987561125075024557254611/267900296794500000000000)]
    bernstein := [(234350765761282726162670766029/685824759793920000000000000000), (30712654145497541303502871981/85728094974240000000000000000), (2913139638542120547301436363/8037008903835000000000000000), (237453987474787426860471913/669750741986250000000000000), (14008069891154608198670741/41859421374140625000000000)]
    reserve := (41830696147/125000000000) }

theorem quarter_025_006_valid : quarter_025_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_025_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_025_006]
  · intro i; fin_cases i <;> norm_num [quarter_025_006]
  · norm_num [quarter_025_006]
  · norm_num [quarter_025_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_025_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_025_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_025_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_025_006]

def quarter_025_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (13296399/50000000), (36703601/50000000)]
    cone := fun i => (![![0, 0, (7208357/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(13296399/100000000), 0, (13296399/50000000), 0, 0], ![0, 0, (68421053/100000000), 0, 0]] i.1) i.2
    mu := ![(16697261/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (448949/100000000)]
    alternative := .zero
    polynomial := [(-11364612184292589064356729/2998487451475600000000000), (-488025723632799/11223725000000), (-179091873550159228802888729/1499243725737800000000000), (-488025723632799/11223725000000), (-346819134916025868541420729/2998487451475600000000000)]
    bernstein := [(136246441847856924563076799/468513664293062500000000000), (2310367049381714429525128261/7496218628689000000000000000), (28154514575963423602974382753/89954623544268000000000000000), (292980077649934007469982920953/959515984472192000000000000000), (2190905933801913779741503162471/7676127875777536000000000000000)]
    reserve := (57083622609/200000000000) }

theorem quarter_025_007_valid : quarter_025_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_025_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_025_007]
  · intro i; fin_cases i <;> norm_num [quarter_025_007]
  · norm_num [quarter_025_007]
  · norm_num [quarter_025_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_025_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_025_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_025_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_025_007]

def quarter_025_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 2, 0, 0, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (24049023/100000000), (75950977/100000000)]
    cone := fun i => (![![0, 0, (18645369/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(187883/1562500), 0, (24049023/100000000), 0, 0], ![0, 0, (72043011/100000000), 0, 0]] i.1) i.2
    mu := ![(1727587/10000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (468331/100000000)]
    alternative := .zero
    polynomial := [(-592130163232521009777523/202270636824250000000000), (-1826546792745471/46833100000000), (-12408257453348347240388773/101135318412125000000000), (-1826546792745471/46833100000000), (-24224384743464173471000023/202270636824250000000000)]
    bernstein := [(122784263339620107957711558377/517812830270080000000000000000), (66124220278493264215192924433/258906415135040000000000000000), (101259237814788241533305556971/388359622702560000000000000000), (104431986989384370034921429/412271361680000000000000000), (7548604663746480273710102537/32363301891880000000000000000)]
    reserve := (5831145327/25000000000) }

theorem quarter_025_008_valid : quarter_025_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_025_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_025_008]
  · intro i; fin_cases i <;> norm_num [quarter_025_008]
  · norm_num [quarter_025_008]
  · norm_num [quarter_025_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_025_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_025_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_025_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_025_008]

def quarter_025_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 2, 0, 0, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (664171/3125000), (2460829/3125000)]
    cone := fun i => (![![0, 0, (3866331/10000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(664171/6250000), 0, (664171/3125000), 0, 0], ![0, 0, (4739011/6250000), 0, 0]] i.1) i.2
    mu := ![(4477937/25000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (489/100000)]
    alternative := .zero
    polynomial := [(-4733832133543288874689/2189711193000000000000), (-1634411257759/47753906250), (-46140063934181650534123/364951865500000000000), (-1634411257759/47753906250), (-272106551471546614330049/2189711193000000000000)]
    bernstein := [(63056820484380790782766031/350353790880000000000000000), (9303894629255031036217799/46713838784000000000000000), (3831329916890693390789357/18685535513600000000000000), (295623248417801293123283/1494842841088000000000000), (63657156070695807467159/358762281861120000000000)]
    reserve := (44358868873/250000000000) }

theorem quarter_025_009_valid : quarter_025_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_025_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_025_009]
  · intro i; fin_cases i <;> norm_num [quarter_025_009]
  · norm_num [quarter_025_009]
  · norm_num [quarter_025_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_025_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_025_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_025_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_025_009]

def quarter_025_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 2, 0, 0, 0, 0, 1]
    lambda := ![(2423651/100000000), (899501/6250000), (899501/6250000), (899501/6250000), (8368383/100000000), (8368383/100000000), (18831767/50000000)]
    cone := fun i => (![![0, 0, (16663541/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (36722091/100000000), 0, 0]] i.1) i.2
    mu := ![(442131/5000000), (239597/6250000), (1/100000000), (1/100000000), (525831/12500000), (1/100000000), (29407/12500000)]
    alternative := .zero
    polynomial := [(-675669801311740857348023935367729/1092038603704409243946000000000000), (-38313227396484814801/2818331591600000000), (-32933628874180337685446416359685229/546019301852204621973000000000000), (-38313227396484814801/2818331591600000000), (-65191587947048934513544808784002729/1092038603704409243946000000000000)]
    bernstein := [(26856681387775185720906571576650799/178919604830930410528112640000000000), (59012214652548533355113218835848621/372749176731105021933568000000000000), (3358782980176804807058284757469289177/20967141191124657483763200000000000000), (453699491746887373401181833279235517/2912102943211757983856000000000000000), (1585333068246583371264172942181011471/10920386037044092439460000000000000000)]
    reserve := (1161375111/8000000000) }

theorem quarter_025_010_valid : quarter_025_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_025_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_025_010]
  · intro i; fin_cases i <;> norm_num [quarter_025_010]
  · norm_num [quarter_025_010]
  · norm_num [quarter_025_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_025_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_025_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_025_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_025_010]

def quarter_025_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 1]
    lambda := ![(1777267/50000000), (14690773/100000000), (14690773/100000000), (14690773/100000000), (3375413/50000000), (3375413/50000000), (7774299/20000000)]
    cone := fun i => (![![0, 0, (16403371/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (19140399/50000000), 0, 0]] i.1) i.2
    mu := ![(4623/50000), (1994149/50000000), (1/100000000), (1/100000000), (4085239/100000000), (1/100000000), (60983/25000000)]
    alternative := .zero
    polynomial := [(-13350406100829420848933090493364453/36747494678613177726384000000000000), (-20431436505696508621/1870910591800000000), (-1139582621647505518813544325752284453/18373747339306588863192000000000000), (-20431436505696508621/1870910591800000000), (-2265814837194181616778155561011204453/36747494678613177726384000000000000)]
    bernstein := [(41630747868215316484572083142552174947/367474946786131777263840000000000000000), (13800866225318265100136115967303057657/113069214395732854542720000000000000000), (2192858219553232474890231024501564732869/17638797445734325308664320000000000000000), (217332520903836402956325173509708088813/1809107430331725672683520000000000000000), (10303246851053403670014005805099418912907/94073586377249734979543040000000000000000)]
    reserve := (21904654107/200000000000) }

theorem quarter_025_011_valid : quarter_025_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_025_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_025_011]
  · intro i; fin_cases i <;> norm_num [quarter_025_011]
  · norm_num [quarter_025_011]
  · norm_num [quarter_025_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_025_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_025_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_025_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_025_011]

def quarter_025_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 2, 0, 0, 0, 0, 1]
    lambda := ![(1357491/25000000), (11179043/50000000), (11179043/50000000), (11179043/50000000), (10077569/100000000), (10077569/100000000), (45879/625000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9676619/100000000), 0, 0]] i.1) i.2
    mu := ![(2307143/100000000), (187789/3125000), (1/100000000), (1/100000000), (6196801/100000000), (1/100000000), (2436293/100000000)]
    alternative := .zero
    polynomial := [(1076923905664208555773523543956995909/13081927128140956091774222000000000000), (-100427736591311572627/183003610470800000000), (-3755028426420085511892362583237124091/6540963564070478045887111000000000000), (-100427736591311572627/183003610470800000000), (-8586980758504379579558248710431244091/13081927128140956091774222000000000000)]
    bernstein := [(4034211864539697436767687867505379071847829/33489733448040847594942008320000000000000000), (1967832519148427792262519962743025879362543/16744866724020423797471004160000000000000000), (2876601741880655562942888366181501452392743/25117300086030635696206506240000000000000000), (466697210977285967054579380431765990740727/4186216681005105949367751040000000000000000), (226871032368429552447270345034663601023109/2093108340502552974683875520000000000000000)]
    reserve := (54194765741/500000000000) }

theorem quarter_025_012_valid : quarter_025_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_025_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_025_012]
  · intro i; fin_cases i <;> norm_num [quarter_025_012]
  · norm_num [quarter_025_012]
  · norm_num [quarter_025_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_025_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_025_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_025_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_025_012]

def quarter_025_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 1]
    lambda := ![(5386457/100000000), (22447103/100000000), (22447103/100000000), (22447103/100000000), (653631/6250000), (653631/6250000), (158901/2500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8945049/100000000), 0, 0]] i.1) i.2
    mu := ![(2105193/100000000), (2981753/50000000), (1/100000000), (1/100000000), (6257309/100000000), (1/100000000), (2644991/100000000)]
    alternative := .zero
    polynomial := [(8794373873178160856146061187943306963/103890391463496619331370051000000000000), (-156946995860315080911/315468393968920000000), (-25691827031495542128239850370877023037/51945195731748309665685025500000000000), (-156946995860315080911/315468393968920000000), (-60178027936169245112625761929697353037/103890391463496619331370051000000000000)]
    bernstein := [(1801007529605355687796000621138956851797363/16622462634159459093019208160000000000000000), (1169401590375219291891686240954243540012521/11081641756106306062012805440000000000000000), (20477460211961496272681865156382541797858489/199469551609913509116230497920000000000000000), (4421441718505611195029836535921333751207721/44326567024425224248051221760000000000000000), (25741291572750123346881912178673816161208563/265959402146551345488307330560000000000000000)]
    reserve := (96786544731/1000000000000) }

theorem quarter_025_013_valid : quarter_025_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_025_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_025_013]
  · intro i; fin_cases i <;> norm_num [quarter_025_013]
  · norm_num [quarter_025_013]
  · norm_num [quarter_025_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_025_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_025_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_025_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_025_013]

def quarter_025_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 2, 0, 0, 0, 0, 1]
    lambda := ![0, (12650513/50000000), (12650513/50000000), (12650513/50000000), (12048461/100000000), (12048461/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (6868967/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3146509/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (6625101/100000000), (1/100000000), (1/100000000), (7080937/100000000), (1/100000000), (314651/10000000)]
    alternative := .zero
    polynomial := [(5423335396513641856848165066949/59043533683314326748000000000000), (-2306454180673/9464430000000), (-3300832316147352858399541189017/9840588947219054458000000000000), (-2306454180673/9464430000000), (-25228329293397759007245412201051/59043533683314326748000000000000)]
    bernstein := [(14773480188290132644965499057874675749/151151446229284676474880000000000000000), (3033062070631010389715692311481283/31489884631100974265600000000000000), (8961810565309776269139838621929383/94469653893302922796800000000000000), (1837755003338307353432843986483/19681177894438108916000000000000), (5423335396513641856848165066949/59043533683314326748000000000000)]
    reserve := (22963291059/250000000000) }

theorem quarter_025_014_valid : quarter_025_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_025_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_025_014]
  · intro i; fin_cases i <;> norm_num [quarter_025_014]
  · norm_num [quarter_025_014]
  · norm_num [quarter_025_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_025_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_025_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_025_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_025_014]

def quarter_025_015 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 1]
    lambda := ![0, (25316541/100000000), (25316541/100000000), (25316541/100000000), (3006297/25000000), (3006297/25000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (31719/390625), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (196277/6250000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3310181/50000000), (1/100000000), (1/100000000), (7081951/100000000), (1/100000000), (196277/6250000)]
    alternative := .zero
    polynomial := [(6606852530226291440753686673/71894239898981613859375000000), (803015363979/2586078906250), (-48609550173214805654472736183/143788479797963227718750000000), (803015363979/2586078906250), (-61823255233667388535980109529/143788479797963227718750000000)]
    bernstein := [(6606852530226291440753686673/71894239898981613859375000000), (3373189434221389970277032899/35947119949490806929687500000), (132160770417684739249150869785417/1380369406060446986100000000000000), (44914710442384495565335602687517/460123135353482328700000000000000), (36608533195029090348932392740557671/368098508282785862960000000000000000)]
    reserve := (45948413527/500000000000) }

theorem quarter_025_015_valid : quarter_025_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_025_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_025_015]
  · intro i; fin_cases i <;> norm_num [quarter_025_015]
  · norm_num [quarter_025_015]
  · norm_num [quarter_025_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_025_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_025_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_025_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_025_015]

def quarter_025_016 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 2, 0, 0, 0, 0, 1]
    lambda := ![0, (12726637/50000000), (12726637/50000000), (12726637/50000000), (11820089/100000000), (11820089/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2349093/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3086869/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (6630589/100000000), (1/100000000), (1/100000000), (886399/12500000), (1/100000000), (308687/10000000)]
    alternative := .zero
    polynomial := [(65827137447936353727047449961/725704302031891422800000000000), (4270864841463/11840337500000), (-125432489957729181655107208439/362852151015945711400000000000), (4270864841463/11840337500000), (-316692117363394717037261866839/725704302031891422800000000000)]
    bernstein := [(184879196631536138831067884253528361/1857803013201642042368000000000000000), (94437139805035230888743060688919561/928901506600821021184000000000000000), (20657933985738613530103010194096669/199050322843033075968000000000000000), (24585101294885056150554814645926361/232225376650205255296000000000000000), (12531033959474236501009066362261961/116112688325102627648000000000000000)]
    reserve := (49757481099/500000000000) }

theorem quarter_025_016_valid : quarter_025_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_025_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_025_016]
  · intro i; fin_cases i <;> norm_num [quarter_025_016]
  · norm_num [quarter_025_016]
  · norm_num [quarter_025_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_025_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_025_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_025_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_025_016]

def quarter_025_017 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 1]
    lambda := ![0, (25599793/100000000), (25599793/100000000), (25599793/100000000), (1160031/10000000), (1160031/10000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (1066417/10000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3029473/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1656609/25000000), (1/100000000), (1/100000000), (3550843/50000000), (1/100000000), (3029473/100000000)]
    alternative := .zero
    polynomial := [(6290309671975638912158836394149/71281784661552756204000000000000), (27300054451681/66264360000000), (-4230619617304515456123596491117/11880297443592126034000000000000), (27300054451681/66264360000000), (-31674027375802731648900415340851/71281784661552756204000000000000)]
    bernstein := [(1231789074994553643487786872787818349/11405085545848440992640000000000000000), (17855635292548481926818160014606067/161774263061680014080000000000000000), (5141991754826361995502800805333760741/45620342183393763970560000000000000000), (3498214458578653027944142120935268341/30413561455595842647040000000000000000), (21405314456093501133859490695318322269/182481368733575055882240000000000000000)]
    reserve := (108003492831/1000000000000) }

theorem quarter_025_017_valid : quarter_025_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_025_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_025_017]
  · intro i; fin_cases i <;> norm_num [quarter_025_017]
  · norm_num [quarter_025_017]
  · norm_num [quarter_025_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_025_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_025_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_025_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_025_017]

def quarter_025_018 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 2, 0, 0, 0, 0, 1]
    lambda := ![0, (25755647/100000000), (25755647/100000000), (25755647/100000000), (1136653/10000000), (1136653/10000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2979961/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (148421/5000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1651927/25000000), (1/100000000), (1/100000000), (88919/1250000), (1/100000000), (2968421/100000000)]
    alternative := .zero
    polynomial := [(147301538449725843313574942869/1744098096632737492000000000000), (76750823589767/165192700000000), (-322160515852936725186740830131/872049048316368746000000000000), (76750823589767/165192700000000), (-791622570155599293687056603131/1744098096632737492000000000000)]
    bernstein := [(524208536868857749436562677117613589/4464891127379807979520000000000000000), (133956224401917475870332182770275063/1116222781844951994880000000000000000), (34206933420877683885315621781559721/279055695461237998720000000000000000), (8729255885974163828363983206758907/69763923865309499680000000000000000), (2226227188845234359220072539260669/17440980966327374920000000000000000)]
    reserve := (58703395213/500000000000) }

theorem quarter_025_018_valid : quarter_025_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_025_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_025_018]
  · intro i; fin_cases i <;> norm_num [quarter_025_018]
  · norm_num [quarter_025_018]
  · norm_num [quarter_025_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_025_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_025_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_025_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_025_018]

def quarter_025_019 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 2, 0, 0, 0, 0, 1]
    lambda := ![0, (25920337/100000000), (25920337/100000000), (25920337/100000000), (2223899/20000000), (2223899/20000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (3289947/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1451953/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1314859/20000000), (1/100000000), (1/100000000), (1781693/25000000), (1/100000000), (1451953/50000000)]
    alternative := .zero
    polynomial := [(16853331329332798508485901753/212590881565008656937500000000), (85276534952139/164357375000000), (-82017003457267181937311246019/212590881565008656937500000000), (85276534952139/164357375000000), (-24717583696649995111449286943/53147720391252164234375000000)]
    bernstein := [(4244346432260056817332733897427/33217325244532602646484375000000), (6942223971493068017584220411149/53147720391252164234375000000000), (6982956351552969563359438707387/52330063154463669400000000000000), (14828639450609048696098574536997/108846531361284432352000000000000), (93108105515259300521147354421/669824808377134968320000000000)]
    reserve := (15971885157/125000000000) }

theorem quarter_025_019_valid : quarter_025_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_025_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_025_019]
  · intro i; fin_cases i <;> norm_num [quarter_025_019]
  · norm_num [quarter_025_019]
  · norm_num [quarter_025_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_025_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_025_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_025_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_025_019]

def quarter_025_020 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 2, 0, 0, 0, 0, 1]
    lambda := ![0, (2609333/10000000), (2609333/10000000), (2609333/10000000), (2172001/20000000), (2172001/20000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (14380439/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2836139/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (203943/3125000), (1/100000000), (1/100000000), (1428303/20000000), (1/100000000), (2836139/100000000)]
    alternative := .zero
    polynomial := [(2559819058390696976824978431601/35248884584058339456000000000000), (37523354037187/65261760000000), (-7144462294616452424911989298399/17624442292029169728000000000000), (37523354037187/65261760000000), (-5616247882541200608882985676133/11749628194686113152000000000000)]
    bernstein := [(803699574037563952003341320504569/5775177250252118336471040000000000), (10270412279782189953639662929574519/72189715628151479205888000000000000), (393480598528366924620635419136626523/2707114336055680470220800000000000000), (334798451842576165993896647225723867/2255928613379733725184000000000000000), (854116955935572939340041224676386881/5639821533449334312960000000000000000)]
    reserve := (139164486077/1000000000000) }

theorem quarter_025_020_valid : quarter_025_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_025_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_025_020]
  · intro i; fin_cases i <;> norm_num [quarter_025_020]
  · norm_num [quarter_025_020]
  · norm_num [quarter_025_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_025_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_025_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_025_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_025_020]

def quarter_025_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 1]
    lambda := ![0, (26274061/100000000), (26274061/100000000), (26274061/100000000), (10588909/100000000), (10588909/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (7789159/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2765341/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (807927/12500000), (1/100000000), (1/100000000), (7157811/100000000), (1/100000000), (2765341/100000000)]
    alternative := .zero
    polynomial := [(915411175974612017668249857457/14215054170780910024000000000000), (204652838704699/323170800000000), (-9133524975733661633279484539129/21322581256171365036000000000000), (204652838704699/323170800000000), (-21013283479391159319563718650629/42645162512342730072000000000000)]
    bernstein := [(344884592816804317256267848554443417/2274408667324945603840000000000000000), (2115437137059960204717920999830238719/13646452003949673623040000000000000000), (12967610047640145579963635232473083033/81878712023698041738240000000000000000), (2942425555603985743745436154390763853/18195269338599564830720000000000000000), (18016839870803133141694681545829372571/109171616031597388984320000000000000000)]
    reserve := (151637037693/1000000000000) }

theorem quarter_025_021_valid : quarter_025_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_025_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_025_021]
  · intro i; fin_cases i <;> norm_num [quarter_025_021]
  · norm_num [quarter_025_021]
  · norm_num [quarter_025_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_025_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_025_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_025_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_025_021]

def quarter_025_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 2, 0, 0, 0, 0, 1]
    lambda := ![0, (26461941/100000000), (26461941/100000000), (26461941/100000000), (10307089/100000000), (10307089/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (16750069/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1345871/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (6386173/100000000), (1/100000000), (1/100000000), (3587857/50000000), (1/100000000), (2691743/100000000)]
    alternative := .zero
    polynomial := [(13442993897114095556520530288657/246700135567163151692000000000000), (443239337623929/638617300000000), (-56119273759369032453232138110343/123350067783581575846000000000000), (443239337623929/638617300000000), (-125681541415852160462984806509343/246700135567163151692000000000000)]
    bernstein := [(104370777134064600388963391371946405057/631552347051937668331520000000000000000), (13336304010787171632477330769970382351/78944043381492208541440000000000000000), (1277319959230579793683676151497706701/7401004067014894550760000000000000000), (8360443428241083953363838403928499/47442333762915990710000000000000000), (533258986584040057752526893253541/2965145860182249419375000000000000)]
    reserve := (82630345387/500000000000) }

theorem quarter_025_022_valid : quarter_025_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_025_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_025_022]
  · intro i; fin_cases i <;> norm_num [quarter_025_022]
  · norm_num [quarter_025_022]
  · norm_num [quarter_025_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_025_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_025_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_025_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_025_022]

def quarter_025_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 1]
    lambda := ![0, (13328183/50000000), (13328183/50000000), (13328183/50000000), (10015451/100000000), (10015451/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (1118281/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (130779/5000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (6294693/100000000), (1/100000000), (1/100000000), (1439053/20000000), (1/100000000), (130779/5000000)]
    alternative := .zero
    polynomial := [(1535436335930785518972777521/35898426699624027000000000000), (14904653813423/19670915625000), (-8713785668767971940202018479/17949213349812013500000000000), (14904653813423/19670915625000), (-18963007673466729399376814479/35898426699624027000000000000)]
    bernstein := [(1010256648738051963287895853049/5609129171816254218750000000000), (1501973341081470703394118473687/8158733340823642500000000000000), (28933428931610397583993453748801/153850400141245830000000000000000), (200524849260020365870172212355219/1044317867625426240000000000000000), (18008184608470331024155197430606481/91899972351037509120000000000000000)]
    reserve := (22513669631/125000000000) }

theorem quarter_025_023_valid : quarter_025_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_025_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_025_023]
  · intro i; fin_cases i <;> norm_num [quarter_025_023]
  · norm_num [quarter_025_023]
  · norm_num [quarter_025_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_025_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_025_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_025_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_025_023]

def quarter_025_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 2, 0, 0, 0, 0, 1]
    lambda := ![0, (13428361/50000000), (13428361/50000000), (13428361/50000000), (4857459/50000000), (4857459/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (19002599/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1268547/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (6189309/100000000), (1/100000000), (1/100000000), (1443299/20000000), (1/100000000), (507419/20000000)]
    alternative := .zero
    polynomial := [(47942566914702295399002763517/1648285762352985756000000000000), (36453394187177/44209350000000), (-142903614766981243118883498161/274714293725497626000000000000), (36453394187177/44209350000000), (-905364255516589754112303752483/1648285762352985756000000000000)]
    bernstein := [(828153331419580783602167604716685437/4219611551623643535360000000000000000), (6510526018973119685999814188109001/32458550397104950272000000000000000), (8645260940061417736659941455442461/42196115516236435353600000000000000), (67894762224207057488081719325257/324585503971049502720000000000000), (5298178615906484023013330543789/24821244421315550208000000000000)]
    reserve := (98131465573/500000000000) }

theorem quarter_025_024_valid : quarter_025_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_025_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_025_024]
  · intro i; fin_cases i <;> norm_num [quarter_025_024]
  · norm_num [quarter_025_024]
  · norm_num [quarter_025_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_025_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_025_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_025_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_025_024]

def quarter_025_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 1]
    lambda := ![0, (6765597/25000000), (6765597/25000000), (6765597/25000000), (9406417/100000000), (9406417/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (20077599/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (153533/6250000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3035217/50000000), (1/100000000), (1/100000000), (7239419/100000000), (1/100000000), (153533/6250000)]
    alternative := .zero
    polynomial := [(23855860278318622378912312717/1799259992189922644800000000000), (45278981187201/50586950000000), (-503328557537381212944990892883/899629996094961322400000000000), (45278981187201/50586950000000), (-1030512975353081048268894098483/1799259992189922644800000000000)]
    bernstein := [(98481890888041988090574787336813/460610558000620197068800000000000), (1006334029160843587389440814999519/4606105580006201970688000000000000), (30833992494815479858991269853929663/138183167400186059120640000000000000), (104922187042872377113498503097419447/460610558000620197068800000000000000), (1070605160001778228312653270846692797/4606105580006201970688000000000000000)]
    reserve := (213807280743/1000000000000) }

theorem quarter_025_025_valid : quarter_025_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_025_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_025_025]
  · intro i; fin_cases i <;> norm_num [quarter_025_025]
  · norm_num [quarter_025_025]
  · norm_num [quarter_025_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_025_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_025_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_025_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_025_025]

def quarter_025_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 2, 0, 0, 0, 0, 1]
    lambda := ![0, (27272749/100000000), (27272749/100000000), (27272749/100000000), (2272719/25000000), (2272719/25000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2111497/10000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2374123/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2969279/50000000), (1/100000000), (1/100000000), (3632021/50000000), (1/100000000), (2374123/100000000)]
    alternative := .zero
    polynomial := [(-251706356793168510501322516743/51207381509200515314000000000000), (57586327695253/59385580000000), (-15458764750520534181865375624243/25603690754600257657000000000000), (57586327695253/59385580000000), (-30665823144247899853229428731743/51207381509200515314000000000000)]
    bernstein := [(30522461448890522884056496827645581137/131090896663553319203840000000000000000), (7796079125987803746826448707638488601/32772724165888329800960000000000000000), (5970963866289759052251039173605785719/24579543124416247350720000000000000000), (507892078636320879846040339038425629/2048295260368020612560000000000000000), (129548055901238470257108994154661417/512073815092005153140000000000000000)]
    reserve := (232834332709/1000000000000) }

theorem quarter_025_026_valid : quarter_025_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_025_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_025_026]
  · intro i; fin_cases i <;> norm_num [quarter_025_026]
  · norm_num [quarter_025_026]
  · norm_num [quarter_025_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_025_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_025_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_025_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_025_026]

def quarter_025_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 1]
    lambda := ![0, (27487193/100000000), (27487193/100000000), (27487193/100000000), (876921/10000000), (876921/10000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (22112459/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1145059/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (5794241/100000000), (1/100000000), (1/100000000), (3645177/50000000), (1/100000000), (2290119/100000000)]
    alternative := .zero
    polynomial := [(-42454646831057710018014443843/1653664318694139596000000000000), (607809428237587/579424100000000), (-540367436046299942947187116843/826832159347069798000000000000), (607809428237587/579424100000000), (-1038280225261542175876359789843/1653664318694139596000000000000)]
    bernstein := [(4191080184925187611598930612675317/16536643186941395960000000000000000), (17124936399623141156350755992422607/66146572747765583840000000000000000), (209822614800314258967103112291117291/793758872973187006080000000000000000), (4680719109877358160321783850808767/17349920720725399040000000000000000), (19100398857585182351492669933264257/69399682882901596160000000000000000)]
    reserve := (31680251983/125000000000) }

theorem quarter_025_027_valid : quarter_025_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_025_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_025_027]
  · intro i; fin_cases i <;> norm_num [quarter_025_027]
  · norm_num [quarter_025_027]
  · norm_num [quarter_025_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_025_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_025_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_025_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_025_027]

def quarter_025_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 2, 0, 0, 0, 0, 1]
    lambda := ![0, (173157/625000), (173157/625000), (173157/625000), (8442321/100000000), (8442321/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (11534049/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8819/400000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (5638103/100000000), (1/100000000), (1/100000000), (1829583/25000000), (1/100000000), (8819/400000)]
    alternative := .zero
    polynomial := [(-249109924285680419097453333/5053961849991729500000000000), (1997201322693/1761907187500), (-1792538466410501394617013333/2526980924995864750000000000), (1997201322693/1761907187500), (-3335967008535322370136573333/5053961849991729500000000000)]
    bernstein := [(3567490133556733398381404018069787/12938142335978827520000000000000000), (1821792003923148759858594068565393/6469071167989413760000000000000000), (929911898900759079425242341380227/3234535583994706880000000000000000), (474461852274321373759115448973353/1617267791997353440000000000000000), (241983516313844637453178535493867/808633895998676720000000000000000)]
    reserve := (275734339669/1000000000000) }

theorem quarter_025_028_valid : quarter_025_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_025_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_025_028]
  · intro i; fin_cases i <;> norm_num [quarter_025_028]
  · norm_num [quarter_025_028]
  · norm_num [quarter_025_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_025_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_025_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_025_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_025_028]

def quarter_025_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 2, 0, 0, 0, 0, 1]
    lambda := ![0, (33333333/100000000), (33333333/100000000), (33333333/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (28623581/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9873603/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (6530147/100000000), (1/100000000), (1/100000000), (270777/3125000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-791352488847721368036173/5803367759488000000000000), (954119357125473/653014700000000), (-2937790811621204592324173/2901683879744000000000000), (954119357125473/653014700000000), (-5084229134394687816612173/5803367759488000000000000)]
    bernstein := [(279023570419861849652590111027/928538841518080000000000000000), (114253662594494344577861152463/371415536607232000000000000000), (140271802598845565369771974273/445698643928678400000000000000), (19124525956096234960326270151/59426485857157120000000000000), (7818190784798868847520642083/23770594342862848000000000000)]
    reserve := (300497467573/1000000000000) }

theorem quarter_025_029_valid : quarter_025_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_025_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_025_029]
  · intro i; fin_cases i <;> norm_num [quarter_025_029]
  · norm_num [quarter_025_029]
  · norm_num [quarter_025_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_025_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_025_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_025_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_025_029]

def quarterTable025 : OwnerTable where
  mode := .quarter
  owners := ![0, 2, 0, 0, 0, 0, 1]
  rows := [quarter_025_000, quarter_025_001, quarter_025_002, quarter_025_003, quarter_025_004, quarter_025_005, quarter_025_006, quarter_025_007, quarter_025_008, quarter_025_009, quarter_025_010, quarter_025_011, quarter_025_012, quarter_025_013, quarter_025_014, quarter_025_015, quarter_025_016, quarter_025_017, quarter_025_018, quarter_025_019, quarter_025_020, quarter_025_021, quarter_025_022, quarter_025_023, quarter_025_024, quarter_025_025, quarter_025_026, quarter_025_027, quarter_025_028, quarter_025_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_025_000_valid
    · exact quarter_025_001_valid
    · exact quarter_025_002_valid
    · exact quarter_025_003_valid
    · exact quarter_025_004_valid
    · exact quarter_025_005_valid
    · exact quarter_025_006_valid
    · exact quarter_025_007_valid
    · exact quarter_025_008_valid
    · exact quarter_025_009_valid
    · exact quarter_025_010_valid
    · exact quarter_025_011_valid
    · exact quarter_025_012_valid
    · exact quarter_025_013_valid
    · exact quarter_025_014_valid
    · exact quarter_025_015_valid
    · exact quarter_025_016_valid
    · exact quarter_025_017_valid
    · exact quarter_025_018_valid
    · exact quarter_025_019_valid
    · exact quarter_025_020_valid
    · exact quarter_025_021_valid
    · exact quarter_025_022_valid
    · exact quarter_025_023_valid
    · exact quarter_025_024_valid
    · exact quarter_025_025_valid
    · exact quarter_025_026_valid
    · exact quarter_025_027_valid
    · exact quarter_025_028_valid
    · exact quarter_025_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
