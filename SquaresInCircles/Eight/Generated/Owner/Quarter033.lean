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

def quarter_033_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 2, 0, 2, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (305109/781250), (476141/781250)]
    cone := fun i => (![![0, 0, (14961777/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(305109/1562500), 0, (305109/781250), 0, 0], ![0, 0, (46788991/100000000), 0, 0]] i.1) i.2
    mu := ![(13862837/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (341629/100000000)]
    alternative := .zero
    polynomial := [(-14374691271790946411340937/1183986785368250000000000), (-9297593879616/133448828125), (-63788844655569788786860937/591993392684125000000000), (-9297593879616/133448828125), (-113202998039348631162380937/1183986785368250000000000)]
    bernstein := [(2990005041502588170728626727/4849609872868352000000000000), (7620368667567275881374279419/12124024682170880000000000000), (57200606057925900106726513837/90930185116281600000000000000), (46860259961119773118474510947/75775154263568000000000000000), (113063918489006412728021519863/189437885658920000000000000000)]
    reserve := (14920975033/25000000000) }

theorem quarter_033_000_valid : quarter_033_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_033_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_033_000]
  · intro i; fin_cases i <;> norm_num [quarter_033_000]
  · norm_num [quarter_033_000]
  · norm_num [quarter_033_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_033_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_033_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_033_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_033_000]

def quarter_033_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (37732553/100000000), (62267447/100000000)]
    cone := fun i => (![![0, 0, (1528617/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(18866277/100000000), 0, (37732553/100000000), 0, 0], ![0, 0, (4953271/10000000), 0, 0]] i.1) i.2
    mu := ![(14163403/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (354441/100000000)]
    alternative := .zero
    polynomial := [(-107611658598710606406360499/10040181445446000000000000), (-2349509744102191/35444100000000), (-181483337459563315242486833/1673363574241000000000000), (-2349509744102191/35444100000000), (-981288366158669285048560499/10040181445446000000000000)]
    bernstein := [(919532253676100215105530441101/1606429031271360000000000000000), (1879851632914358466935883430559/3212858062542720000000000000000), (3767188926728837572299399960181/6425716125085440000000000000000), (7404713308036821615973784746679/12851432250170880000000000000000), (14266927128878180023579413088861/25702864500341760000000000000000)]
    reserve := (277535741759/500000000000) }

theorem quarter_033_001_valid : quarter_033_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_033_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_033_001]
  · intro i; fin_cases i <;> norm_num [quarter_033_001]
  · norm_num [quarter_033_001]
  · norm_num [quarter_033_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_033_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_033_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_033_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_033_001]

def quarter_033_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 2, 0, 2, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (36281179/100000000), (63718821/100000000)]
    cone := fun i => (![![0, 0, (15642471/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1814059/10000000), 0, (36281179/100000000), 0, 0], ![0, 0, (6547619/12500000), 0, 0]] i.1) i.2
    mu := ![(7246767/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (367987/100000000)]
    alternative := .zero
    polynomial := [(-8328927597030419362173933/888905349343000000000000), (-2311793950369959/36798700000000), (-48640910973048999170613933/444452674671500000000000), (-2311793950369959/36798700000000), (-88952894349067578979053933/888905349343000000000000)]
    bernstein := [(1201621007407386091306135973187/2275597694318080000000000000000), (308040043995528656192395392597/568899423579520000000000000000), (77265236295115823350674097207/142224855894880000000000000000), (18976090232022837413552977017/35556213973720000000000000000), (4559949838646291704679922027/8889053493430000000000000000)]
    reserve := (128246214347/250000000000) }

theorem quarter_033_002_valid : quarter_033_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_033_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_033_002]
  · intro i; fin_cases i <;> norm_num [quarter_033_002]
  · norm_num [quarter_033_002]
  · norm_num [quarter_033_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_033_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_033_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_033_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_033_002]

def quarter_033_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (34687529/100000000), (65312471/100000000)]
    cone := fun i => (![![0, 0, (32067399/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(3468753/20000000), 0, (34687529/100000000), 0, 0], ![0, 0, (27669903/50000000), 0, 0]] i.1) i.2
    mu := ![(14856027/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (95581/25000000)]
    alternative := .zero
    polynomial := [(-22993938576098725413408389/2839907833374000000000000), (-2265528231874159/38232400000000), (-157232236230409305195663389/1419953916687000000000000), (-2265528231874159/38232400000000), (-291470533884719884977918389/2839907833374000000000000)]
    bernstein := [(13721315095064621478401170291/28399078333740000000000000000), (56494547290367897220467356867/113596313334960000000000000000), (681225850798745907422906180437/1363155760019520000000000000000), (891783001585839687797971583423/1817541013359360000000000000000), (3418956771277319837318513405851/7270164053437440000000000000000)]
    reserve := (470272300067/1000000000000) }

theorem quarter_033_003_valid : quarter_033_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_033_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_033_003]
  · intro i; fin_cases i <;> norm_num [quarter_033_003]
  · norm_num [quarter_033_003]
  · norm_num [quarter_033_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_033_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_033_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_033_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_033_003]

def quarter_033_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 2, 0, 2, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (32937947/100000000), (67062053/100000000)]
    cone := fun i => (![![0, 0, (2057901/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(8234487/50000000), 0, (32937947/100000000), 0, 0], ![0, 0, (29207921/50000000), 0, 0]] i.1) i.2
    mu := ![(3813497/25000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (79503/20000000)]
    alternative := .zero
    polynomial := [(-522976290930603728141567/75796112997750000000000), (-2208886347425191/39751500000000), (-1419268948894550494390689/12632685499625000000000), (-2208886347425191/39751500000000), (-7992637402436699238202567/75796112997750000000000)]
    bernstein := [(84874092072739102667061094153/194038049274240000000000000000), (8777224093450606029420858503/19403804927424000000000000000), (294530147709546860396101443/646793497580800000000000000), (86680303311943665214532231/194038049274240000000000000), (8277382639847301395568137/19403804927424000000000000)]
    reserve := (426585541897/1000000000000) }

theorem quarter_033_004_valid : quarter_033_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_033_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_033_004]
  · intro i; fin_cases i <;> norm_num [quarter_033_004]
  · norm_num [quarter_033_004]
  · norm_num [quarter_033_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_033_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_033_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_033_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_033_004]

def quarter_033_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (31017243/100000000), (68982757/100000000)]
    cone := fun i => (![![0, 0, (8467363/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7754311/50000000), 0, (31017243/100000000), 0, 0], ![0, 0, (30808081/50000000), 0, 0]] i.1) i.2
    mu := ![(15690873/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (41363/10000000)]
    alternative := .zero
    polynomial := [(-3751957175530520117015977/649021579899000000000000), (-2139654936678951/41363000000000), (-5299802024152296461536711/46358684278500000000000), (-2139654936678951/41363000000000), (-70445271162601630344497977/649021579899000000000000)]
    bernstein := [(64865702008638222482352647/166149524454144000000000000), (674792094324244282489899079/1661495244541440000000000000), (20424339739921842881447883077/49844857336243200000000000000), (9529763332552959388327432721/23735646350592000000000000000), (633906697069892355947829894503/1661495244541440000000000000000)]
    reserve := (381527843159/1000000000000) }

theorem quarter_033_005_valid : quarter_033_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_033_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_033_005]
  · intro i; fin_cases i <;> norm_num [quarter_033_005]
  · norm_num [quarter_033_005]
  · norm_num [quarter_033_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_033_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_033_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_033_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_033_005]

def quarter_033_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 2, 0, 2, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (7227123/25000000), (17772877/25000000)]
    cone := fun i => (![![0, 0, (6980963/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7227123/50000000), 0, (7227123/25000000), 0, 0], ![0, 0, (32474227/50000000), 0, 0]] i.1) i.2
    mu := ![(16170531/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (430747/100000000)]
    alternative := .zero
    polynomial := [(-1270666289333411194334611/267900296794500000000000), (-128446768142871/2692168750000), (-15629113707204217875794611/133950148397250000000000), (-128446768142871/2692168750000), (-29987561125075024557254611/267900296794500000000000)]
    bernstein := [(234350765761282726162670766029/685824759793920000000000000000), (30712654145497541303502871981/85728094974240000000000000000), (2913139638542120547301436363/8037008903835000000000000000), (237453987474787426860471913/669750741986250000000000000), (14008069891154608198670741/41859421374140625000000000)]
    reserve := (41830696147/125000000000) }

theorem quarter_033_006_valid : quarter_033_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_033_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_033_006]
  · intro i; fin_cases i <;> norm_num [quarter_033_006]
  · norm_num [quarter_033_006]
  · norm_num [quarter_033_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_033_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_033_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_033_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_033_006]

def quarter_033_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (13296399/50000000), (36703601/50000000)]
    cone := fun i => (![![0, 0, (7208357/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(13296399/100000000), 0, (13296399/50000000), 0, 0], ![0, 0, (68421053/100000000), 0, 0]] i.1) i.2
    mu := ![(16697261/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (448949/100000000)]
    alternative := .zero
    polynomial := [(-11364612184292589064356729/2998487451475600000000000), (-488025723632799/11223725000000), (-179091873550159228802888729/1499243725737800000000000), (-488025723632799/11223725000000), (-346819134916025868541420729/2998487451475600000000000)]
    bernstein := [(136246441847856924563076799/468513664293062500000000000), (2310367049381714429525128261/7496218628689000000000000000), (28154514575963423602974382753/89954623544268000000000000000), (292980077649934007469982920953/959515984472192000000000000000), (2190905933801913779741503162471/7676127875777536000000000000000)]
    reserve := (57083622609/200000000000) }

theorem quarter_033_007_valid : quarter_033_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_033_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_033_007]
  · intro i; fin_cases i <;> norm_num [quarter_033_007]
  · norm_num [quarter_033_007]
  · norm_num [quarter_033_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_033_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_033_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_033_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_033_007]

def quarter_033_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 2, 0, 2, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (24049023/100000000), (75950977/100000000)]
    cone := fun i => (![![0, 0, (18645369/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(187883/1562500), 0, (24049023/100000000), 0, 0], ![0, 0, (72043011/100000000), 0, 0]] i.1) i.2
    mu := ![(1727587/10000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (468331/100000000)]
    alternative := .zero
    polynomial := [(-592130163232521009777523/202270636824250000000000), (-1826546792745471/46833100000000), (-12408257453348347240388773/101135318412125000000000), (-1826546792745471/46833100000000), (-24224384743464173471000023/202270636824250000000000)]
    bernstein := [(122784263339620107957711558377/517812830270080000000000000000), (66124220278493264215192924433/258906415135040000000000000000), (101259237814788241533305556971/388359622702560000000000000000), (104431986989384370034921429/412271361680000000000000000), (7548604663746480273710102537/32363301891880000000000000000)]
    reserve := (5831145327/25000000000) }

theorem quarter_033_008_valid : quarter_033_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_033_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_033_008]
  · intro i; fin_cases i <;> norm_num [quarter_033_008]
  · norm_num [quarter_033_008]
  · norm_num [quarter_033_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_033_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_033_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_033_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_033_008]

def quarter_033_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 2, 0, 2, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (664171/3125000), (2460829/3125000)]
    cone := fun i => (![![0, 0, (3866331/10000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(664171/6250000), 0, (664171/3125000), 0, 0], ![0, 0, (4739011/6250000), 0, 0]] i.1) i.2
    mu := ![(4477937/25000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (489/100000)]
    alternative := .zero
    polynomial := [(-4733832133543288874689/2189711193000000000000), (-1634411257759/47753906250), (-46140063934181650534123/364951865500000000000), (-1634411257759/47753906250), (-272106551471546614330049/2189711193000000000000)]
    bernstein := [(63056820484380790782766031/350353790880000000000000000), (9303894629255031036217799/46713838784000000000000000), (3831329916890693390789357/18685535513600000000000000), (295623248417801293123283/1494842841088000000000000), (63657156070695807467159/358762281861120000000000)]
    reserve := (44358868873/250000000000) }

theorem quarter_033_009_valid : quarter_033_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_033_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_033_009]
  · intro i; fin_cases i <;> norm_num [quarter_033_009]
  · norm_num [quarter_033_009]
  · norm_num [quarter_033_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_033_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_033_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_033_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_033_009]

def quarter_033_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 2, 0, 2, 0, 0, 1]
    lambda := ![(961123/100000000), (5819159/100000000), (5819159/100000000), (11652329/100000000), (11652329/100000000), (11652329/100000000), (13110893/25000000)]
    cone := fun i => (![![0, 0, (25023797/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (10226537/20000000), 0, 0]] i.1) i.2
    mu := ![(6019083/50000000), (387041/25000000), (1/100000000), (411381/12500000), (1/100000000), (1/100000000), (40947/12500000)]
    alternative := .zero
    polynomial := [(-2621946209759481056922648160350007/2906831479273937651646000000000000), (-118767165372032488819/6339267130800000000), (-121769642348952322461848480261715007/1453415739636968825823000000000000), (-118767165372032488819/6339267130800000000), (-240917338488145163866774312363080007/2906831479273937651646000000000000)]
    bernstein := [(70089912596317863331956489157774817/476255269564241944845680640000000000), (52765449909721106340871713364610681/330732826086279128365056000000000000), (9103272100031628845015019033071547191/55811164402059602911603200000000000000), (408144389817058904889431445520376137/2583850203799055690352000000000000000), (4190235862836563747136727778710398593/29068314792739376516460000000000000000)]
    reserve := (28830263417/200000000000) }

theorem quarter_033_010_valid : quarter_033_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_033_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_033_010]
  · intro i; fin_cases i <;> norm_num [quarter_033_010]
  · norm_num [quarter_033_010]
  · norm_num [quarter_033_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_033_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_033_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_033_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_033_010]

def quarter_033_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 1]
    lambda := ![(342143/25000000), (139159/2500000), (139159/2500000), (9990677/100000000), (9990677/100000000), (9990677/100000000), (14381669/25000000)]
    cone := fun i => (![![0, 0, (27212097/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (14163123/25000000), 0, 0]] i.1) i.2
    mu := ![(1655089/12500000), (1513433/100000000), (1/100000000), (90307/3125000), (1/100000000), (1/100000000), (360999/100000000)]
    alternative := .zero
    polynomial := [(-24188799634725008104983901096391483/40830243520491554217070500000000000), (-218287067928736143869/13658694989175000000), (-1869499492204912899117448424281511483/20415121760245777108535250000000000), (-218287067928736143869/13658694989175000000), (-3714810184775100790129912947466631483/40830243520491554217070500000000000)]
    bernstein := [(4394781253068341134234450787065960213/45366937244990615796745000000000000000), (60283432764471471631263763066134765817/544403246939887389560940000000000000000), (2253555234420575641197468203624963384059/19598516889835946024193840000000000000000), (2866884105470721969660748735249522622759/26131355853114594698925120000000000000000), (242067408095926539877982018449697435597/2549400571035570214529280000000000000000)]
    reserve := (94950715413/1000000000000) }

theorem quarter_033_011_valid : quarter_033_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_033_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_033_011]
  · intro i; fin_cases i <;> norm_num [quarter_033_011]
  · norm_num [quarter_033_011]
  · norm_num [quarter_033_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_033_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_033_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_033_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_033_011]

def quarter_033_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 2, 0, 2, 0, 0, 1]
    lambda := ![(1668513/50000000), (12644441/100000000), (12644441/100000000), (22247979/100000000), (22247979/100000000), (22247979/100000000), (926031/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (10253721/100000000), 0, 0]] i.1) i.2
    mu := ![(1442139/100000000), (21399/625000), (1/100000000), (6466113/100000000), (1/100000000), (1/100000000), (2843407/50000000)]
    alternative := .zero
    polynomial := [(5846198812869764461190714492867461/72049729752354658640616000000000000), (-7203980280210983069/23179453864000000000), (-6271619488714783847418439329792539/36024864876177329320308000000000000), (-7203980280210983069/23179453864000000000), (-18389437790299332156027593152452539/72049729752354658640616000000000000)]
    bernstein := [(19107691609740022320230868948851560261141/184447308166027926119976960000000000000000), (494051754921405591182367628812644057813/4853876530684945424209920000000000000000), (1975508029585956650564599041237502396321/19762211589217277798568960000000000000000), (323211564658740373594628934672271062769/3293701931536212966428160000000000000000), (1109943598476256780858511853772860496261/11527956760376745382498560000000000000000)]
    reserve := (48141384529/500000000000) }

theorem quarter_033_012_valid : quarter_033_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_033_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_033_012]
  · intro i; fin_cases i <;> norm_num [quarter_033_012]
  · norm_num [quarter_033_012]
  · norm_num [quarter_033_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_033_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_033_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_033_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_033_012]

def quarter_033_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 1]
    lambda := ![(779649/25000000), (12362259/100000000), (12362259/100000000), (712709/3125000), (712709/3125000), (712709/3125000), (3736823/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2402327/25000000), 0, 0]] i.1) i.2
    mu := ![(1229841/100000000), (3296893/100000000), (1/100000000), (3277471/50000000), (1/100000000), (1/100000000), (1181077/20000000)]
    alternative := .zero
    polynomial := [(1301099733219653627359969429468457861/15695345839083772304139471000000000000), (-267339331148835160441/973471123440250000000), (-1116385158171504185513375167208964139/7847672919541886152069735500000000000), (-267339331148835160441/973471123440250000000), (-3533870049562661998386719763886386139/15695345839083772304139471000000000000)]
    bernstein := [(241848174039720861518202052671396708142661/2511255334253403568662315360000000000000000), (52829013113039495105555799276752802585229/558056740945200793036070080000000000000000), (2803027482003538852425956102414883050798783/30135064011040842823947784320000000000000000), (203920991369896872604674985618146106100029/2232226963780803172144280320000000000000000), (3603272980654055251575789107430151160689061/40180085348054457098597045760000000000000000)]
    reserve := (89678081801/1000000000000) }

theorem quarter_033_013_valid : quarter_033_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_033_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_033_013]
  · intro i; fin_cases i <;> norm_num [quarter_033_013]
  · norm_num [quarter_033_013]
  · norm_num [quarter_033_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_033_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_033_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_033_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_033_013]

def quarter_033_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 2, 0, 2, 0, 0, 1]
    lambda := ![0, (12928073/100000000), (12928073/100000000), (12357309/50000000), (12357309/50000000), (12357309/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (1754919/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6454333/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (338523/10000000), (1/100000000), (7047677/100000000), (1/100000000), (1/100000000), (3227167/50000000)]
    alternative := .zero
    polynomial := [(53377355192143411772494331567/615950198776257268560000000000), (-7025593206901/56420500000000), (-298075547687744728550291387/3241843151453985624000000000), (-7025593206901/56420500000000), (-110011709252814910197049695097/615950198776257268560000000000)]
    bernstein := [(141467130523821576133856159389309703/1576832508867218607513600000000000000), (10959613865569949052437273069939/123190039755251453712000000000000), (52156989718347192638071932163807/591312190825206977817600000000000), (13464181528412882173113144011/153987549694064317140000000000), (53377355192143411772494331567/615950198776257268560000000000)]
    reserve := (43329278323/500000000000) }

theorem quarter_033_014_valid : quarter_033_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_033_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_033_014]
  · intro i; fin_cases i <;> norm_num [quarter_033_014]
  · norm_num [quarter_033_014]
  · norm_num [quarter_033_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_033_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_033_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_033_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_033_014]

def quarter_033_015 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 1]
    lambda := ![0, (12962477/100000000), (12962477/100000000), (12345841/50000000), (12345841/50000000), (12345841/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (4157603/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6448343/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (847433/25000000), (1/100000000), (7046579/100000000), (1/100000000), (1/100000000), (806043/12500000)]
    alternative := .zero
    polynomial := [(6675249004963802438070157644911/77012618584157686416000000000000), (53892833262631/338973200000000), (-3613596942127848836506102682089/38506309292078843208000000000000), (53892833262631/338973200000000), (-13902442889219500111082363009089/77012618584157686416000000000000)]
    bernstein := [(6675249004963802438070157644911/77012618584157686416000000000000), (6751774748969423820362691646661/77012618584157686416000000000000), (414838338852380874986184519110009/4679247711442492339200000000000000), (11044184907970944308462201871577261/123220189734652298265600000000000000), (17861173423428834837204893355557666111/197152303575443677224960000000000000000)]
    reserve := (43338670517/500000000000) }

theorem quarter_033_015_valid : quarter_033_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_033_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_033_015]
  · intro i; fin_cases i <;> norm_num [quarter_033_015]
  · norm_num [quarter_033_015]
  · norm_num [quarter_033_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_033_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_033_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_033_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_033_015]

def quarter_033_016 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 2, 0, 2, 0, 0, 1]
    lambda := ![0, (13264361/100000000), (13264361/100000000), (12245213/50000000), (12245213/50000000), (12245213/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (4896693/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (799473/12500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (863843/25000000), (1/100000000), (8797/125000), (1/100000000), (1/100000000), (1279157/20000000)]
    alternative := .zero
    polynomial := [(13373640006992256453528008193/155529667946043952000000000000), (64951503658173/345537200000000), (-7987259262931526807035028807/77764833973021976000000000000), (64951503658173/345537200000000), (-29348158532855310067598065807/155529667946043952000000000000)]
    bernstein := [(36083158840078221861594678911031793/398155949941872517120000000000000000), (18269495916607327858203068863637393/199077974970936258560000000000000000), (27743340234530120463157002487766179/298616962456404387840000000000000000), (4679975910432098425124206826125793/49769493742734064640000000000000000), (2367830400138003377964900183368593/24884746871367032320000000000000000)]
    reserve := (18125138577/200000000000) }

theorem quarter_033_016_valid : quarter_033_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_033_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_033_016]
  · intro i; fin_cases i <;> norm_num [quarter_033_016]
  · norm_num [quarter_033_016]
  · norm_num [quarter_033_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_033_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_033_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_033_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_033_016]

def quarter_033_017 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 1]
    lambda := ![0, (3396331/25000000), (3396331/25000000), (24276451/100000000), (24276451/100000000), (24276451/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (707409/12500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (99061/1562500), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (879131/25000000), (1/100000000), (878669/12500000), (1/100000000), (1/100000000), (99061/1562500)]
    alternative := .zero
    polynomial := [(409011957371251643643712773/4839283534027888000000000000), (2402595116379/10989137500000), (-274871144183085037058591227/2419641767013944000000000000), (2402595116379/10989137500000), (-958754245737421717760895227/4839283534027888000000000000)]
    bernstein := [(73706459450109766382524437003173/774285365444462080000000000000000), (2047040307877358735334924753703/21213297683409920000000000000000), (908648712483852206697778341829271/9291424385333544960000000000000000), (8407481126912413074654100977327/84853190733639680000000000000000), (1243361127491539588216043707829013/12388565847111393280000000000000000)]
    reserve := (19038577439/200000000000) }

theorem quarter_033_017_valid : quarter_033_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_033_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_033_017]
  · intro i; fin_cases i <;> norm_num [quarter_033_017]
  · norm_num [quarter_033_017]
  · norm_num [quarter_033_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_033_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_033_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_033_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_033_017]

def quarter_033_018 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 2, 0, 2, 0, 0, 1]
    lambda := ![0, (2784801/20000000), (2784801/20000000), (24050663/100000000), (24050663/100000000), (24050663/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (64441/1000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3140469/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (111633/3125000), (1/100000000), (3511053/50000000), (1/100000000), (1/100000000), (6280939/100000000)]
    alternative := .zero
    polynomial := [(60220828643773693914249227/732681590486641818750000000), (59818453747/238150400000), (-5939027725366191976217323319/46891621791145076400000000000), (59818453747/238150400000), (-9793160758567708386729273847/46891621791145076400000000000)]
    bernstein := [(12054401203721703360250433047204793/120042551785331395584000000000000000), (235221433124321929221804410316737/2308510611256372992000000000000000), (2326436747691306864253060189494281/22507978459749636672000000000000000), (15123718752354997980209279085043/144281913203523312000000000000000), (49833621776141066297715048049253/468916217911450764000000000000000)]
    reserve := (20083547083/200000000000) }

theorem quarter_033_018_valid : quarter_033_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_033_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_033_018]
  · intro i; fin_cases i <;> norm_num [quarter_033_018]
  · norm_num [quarter_033_018]
  · norm_num [quarter_033_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_033_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_033_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_033_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_033_018]

def quarter_033_019 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 2, 0, 2, 0, 0, 1]
    lambda := ![0, (3569749/25000000), (3569749/25000000), (23814003/100000000), (23814003/100000000), (23814003/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (1449893/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6219133/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (226353/6250000), (1/100000000), (7016121/100000000), (1/100000000), (1/100000000), (3109567/50000000)]
    alternative := .zero
    polynomial := [(8314124974925592560300150390459/105351800708299376448000000000000), (5175754086857/18108240000000), (-7481854006425943459352546349541/52675900354149688224000000000000), (5175754086857/18108240000000), (-23277832987777479479005243089541/105351800708299376448000000000000)]
    bernstein := [(112034703835317013531812509655592259/1053518007082993764480000000000000000), (30341412513478553006973298382821693/280938135222131670528000000000000000), (221795055264033112161287415391166333/2022754573599348027801600000000000000), (4002112834284417434295120053155109/35960081308432853827584000000000000), (1949277274200930150718569830059571/17260839028047769837240320000000000)]
    reserve := (106343416137/1000000000000) }

theorem quarter_033_019_valid : quarter_033_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_033_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_033_019]
  · intro i; fin_cases i <;> norm_num [quarter_033_019]
  · norm_num [quarter_033_019]
  · norm_num [quarter_033_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_033_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_033_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_033_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_033_019]

def quarter_033_020 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 2, 0, 2, 0, 0, 1]
    lambda := ![0, (457777/3125000), (457777/3125000), (368241/1562500), (368241/1562500), (368241/1562500), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (31536/390625), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3077369/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3663813/100000000), (1/100000000), (7011643/100000000), (1/100000000), (1/100000000), (6154739/100000000)]
    alternative := .zero
    polynomial := [(2948563745201983396034830464889/39527809197152858225250000000000), (153988858368/477058984375), (-3160788709908452223525214223111/19763904598576429112625000000000), (153988858368/477058984375), (-9270141165018887843085258911111/39527809197152858225250000000000)]
    bernstein := [(731927873281058855005432411484641/6476236258861524291624960000000000), (9298914263944371253225307417646991/80952953235769053645312000000000000), (354308131263336008892166539091705747/3035735746341339511699200000000000000), (299908472420759605331520730988962963/2529779788617782926416000000000000000), (761369897763655107024301357088840809/6324449471544457316040000000000000000)]
    reserve := (56508737793/500000000000) }

theorem quarter_033_020_valid : quarter_033_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_033_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_033_020]
  · intro i; fin_cases i <;> norm_num [quarter_033_020]
  · norm_num [quarter_033_020]
  · norm_num [quarter_033_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_033_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_033_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_033_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_033_020]

def quarter_033_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 1]
    lambda := ![0, (15032171/100000000), (15032171/100000000), (11655943/50000000), (11655943/50000000), (11655943/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (8912819/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6088003/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3697913/100000000), (1/100000000), (70089/1000000), (1/100000000), (1/100000000), (1522001/25000000)]
    alternative := .zero
    polynomial := [(2320231308253138766263048901/33572495498057724000000000000), (133979019300049/369791300000000), (-3030534743911541478137254099/16786247749028862000000000000), (133979019300049/369791300000000), (-8381300796076221722537557099/33572495498057724000000000000)]
    bernstein := [(647234117122498540522411413322181/5371599279689235840000000000000000), (1316574679072774936873196867883889/10743198559378471680000000000000000), (8031742962416003711010106185859223/64459191356270830080000000000000000), (5442498387260294143354776103617929/42972794237513886720000000000000000), (11060678873822348714119353963642101/85945588475027773440000000000000000)]
    reserve := (60245941983/500000000000) }

theorem quarter_033_021_valid : quarter_033_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_033_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_033_021]
  · intro i; fin_cases i <;> norm_num [quarter_033_021]
  · norm_num [quarter_033_021]
  · norm_num [quarter_033_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_033_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_033_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_033_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_033_021]

def quarter_033_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 2, 0, 2, 0, 0, 1]
    lambda := ![0, (1928437/12500000), (1928437/12500000), (1440521/6250000), (1440521/6250000), (1440521/6250000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (9765407/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (752397/12500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (232699/6250000), (1/100000000), (3504047/50000000), (1/100000000), (1/100000000), (6019177/100000000)]
    alternative := .zero
    polynomial := [(19582360172107149920797955069089/314109830224603006784000000000000), (18831972178859/46539800000000), (-32054474503781719639336869738911/157054915112301503392000000000000), (18831972178859/46539800000000), (-83691309179670589199471694546911/314109830224603006784000000000000)]
    bernstein := [(103589351819827458787429702290757861889/804121165374983697367040000000000000000), (13177763718773079193327996710081358527/100515145671872962170880000000000000000), (1256853109974351448999687705533489727/9423294906738090203520000000000000000), (106521585844547093727756346642562499/785274575561507516960000000000000000), (6768959155395437606782646702572041/49079660972594219810000000000000000)]
    reserve := (128823063339/1000000000000) }

theorem quarter_033_022_valid : quarter_033_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_033_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_033_022]
  · intro i; fin_cases i <;> norm_num [quarter_033_022]
  · norm_num [quarter_033_022]
  · norm_num [quarter_033_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_033_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_033_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_033_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_033_022]

def quarter_033_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 1]
    lambda := ![0, (3166689/20000000), (3166689/20000000), (22777703/100000000), (22777703/100000000), (22777703/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (212557/2000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5948499/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (747789/20000000), (1/100000000), (54761/781250), (1/100000000), (1/100000000), (11897/200000)]
    alternative := .zero
    polynomial := [(60298835442067421670407777/1113550319508144000000000000), (224367304591/498526000000), (-128543692064857867402992223/556775159754072000000000000), (224367304591/498526000000), (-317386219571783156476392223/1113550319508144000000000000)]
    bernstein := [(24023445488482115310724714313/173992237423147500000000000000), (391380043639312556869639830109/2783875798770360000000000000000), (4780517762073871954047029778959/33406509585244320000000000000000), (51886957060565695016686626685633/356336102242606080000000000000000), (422249742233393483965867355543297/2850688817940848640000000000000000)]
    reserve := (27614387681/200000000000) }

theorem quarter_033_023_valid : quarter_033_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_033_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_033_023]
  · intro i; fin_cases i <;> norm_num [quarter_033_023]
  · norm_num [quarter_033_023]
  · norm_num [quarter_033_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_033_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_033_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_033_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_033_023]

def quarter_033_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 2, 0, 2, 0, 0, 1]
    lambda := ![0, (1624867/10000000), (1624867/10000000), (22500887/100000000), (22500887/100000000), (22500887/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (5748411/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5876207/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1872307/50000000), (1/100000000), (7012993/100000000), (1/100000000), (1/100000000), (367263/6250000)]
    alternative := .zero
    polynomial := [(316588283410475888988486493/7133636042748569250000000000), (9340403336337/18723070000000), (-465750931742350150732621441/1783409010687142312500000000), (9340403336337/18723070000000), (-2179592010379876491918972257/7133636042748569250000000000)]
    bernstein := [(2708343670857486450218428393087423/18262108269436337280000000000000000), (21222532242977887459040760692779/140477755918741056000000000000000), (1960103680726522261716721431799/12741005769374188800000000000000), (12941257441443374699472065659/82633974069847680000000000000), (17120887293452096659857511631/107424166290801984000000000000)]
    reserve := (148303998141/1000000000000) }

theorem quarter_033_024_valid : quarter_033_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_033_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_033_024]
  · intro i; fin_cases i <;> norm_num [quarter_033_024]
  · norm_num [quarter_033_024]
  · norm_num [quarter_033_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_033_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_033_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_033_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_033_024]

def quarter_033_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 1]
    lambda := ![0, (16671873/100000000), (16671873/100000000), (22218751/100000000), (22218751/100000000), (22218751/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (1236887/10000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2901263/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3739711/100000000), (1/100000000), (7018977/100000000), (1/100000000), (1/100000000), (5802527/100000000)]
    alternative := .zero
    polynomial := [(294389180973060658990893905327/8959424409412947057000000000000), (20621222979351/37397110000000), (-1322823077884143005411193047173/4479712204706473528500000000000), (20621222979351/37397110000000), (-2940035336741346669813279999673/8959424409412947057000000000000)]
    bernstein := [(21531535525047957554330517285559/134918391106453790976000000000000), (1243374072838270578153723556696863/7645375496032381488640000000000000), (113996158673837080713009017362530653/688083794642914333977600000000000000), (128987675136799126317369341848777719/764537549603238148864000000000000000), (3939414176414236427744342477884522007/22936126488097144465920000000000000000)]
    reserve := (159589329137/1000000000000) }

theorem quarter_033_025_valid : quarter_033_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_033_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_033_025]
  · intro i; fin_cases i <;> norm_num [quarter_033_025]
  · norm_num [quarter_033_025]
  · norm_num [quarter_033_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_033_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_033_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_033_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_033_025]

def quarter_033_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 2, 0, 2, 0, 0, 1]
    lambda := ![0, (17101819/100000000), (17101819/100000000), (21932121/100000000), (21932121/100000000), (21932121/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (3310121/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5727671/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3723869/100000000), (1/100000000), (3513729/50000000), (1/100000000), (1/100000000), (715959/12500000)]
    alternative := .zero
    polynomial := [(60550174620478887956393370971/3122694913628106153000000000000), (56609090210099/93096725000000), (-520957687469161756500036362029/1561347456814053076500000000000), (56609090210099/93096725000000), (-1102465549558802400956466095029/3122694913628106153000000000000)]
    bernstein := [(1375006712111167627277859149815611611/7994098978887951751680000000000000000), (350411024947919627291390421314754403/1998524744721987937920000000000000000), (267803996824696926052485473914920557/1498893558541490953440000000000000000), (22733519107847707375521064972116287/124907796545124246120000000000000000), (5787584288315266816546266024760451/31226949136281061530000000000000000)]
    reserve := (21500339121/125000000000) }

theorem quarter_033_026_valid : quarter_033_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_033_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_033_026]
  · intro i; fin_cases i <;> norm_num [quarter_033_026]
  · norm_num [quarter_033_026]
  · norm_num [quarter_033_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_033_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_033_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_033_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_033_026]

def quarter_033_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 1]
    lambda := ![0, (3507467/20000000), (3507467/20000000), (21641777/100000000), (21641777/100000000), (21641777/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (3527039/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5651847/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3696833/100000000), (1/100000000), (7038509/100000000), (1/100000000), (1/100000000), (5651847/100000000)]
    alternative := .zero
    polynomial := [(276154705889080683243968898739/73531073013769359229500000000000), (12370972900213/18484165000000), (-13849546966018952829060900423761/36765536506884679614750000000000), (12370972900213/18484165000000), (-27975248637926986341365769746261/73531073013769359229500000000000)]
    bernstein := [(136491055125627201125603283948173059/735310730137693592295000000000000000), (556678975268015641704778240700664889/2941242920550774369180000000000000000), (234786173583294603162550705012883633/1217066036089975601040000000000000000), (1321438850885498446655971386683739107/6722840961258912843840000000000000000), (185653506379710527841892554775817393/927288408449505219840000000000000000)]
    reserve := (92811820589/500000000000) }

theorem quarter_033_027_valid : quarter_033_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_033_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_033_027]
  · intro i; fin_cases i <;> norm_num [quarter_033_027]
  · norm_num [quarter_033_027]
  · norm_num [quarter_033_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_033_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_033_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_033_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_033_027]

def quarter_033_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 2, 0, 2, 0, 0, 1]
    lambda := ![0, (17977319/100000000), (17977319/100000000), (10674227/50000000), (10674227/50000000), (10674227/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2993689/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1393811/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3658457/100000000), (1/100000000), (3526087/50000000), (1/100000000), (1/100000000), (1115049/20000000)]
    alternative := .zero
    polynomial := [(-164540975715895772112409301239/11507339281117604152800000000000), (53818502139791/73169140000000), (-2444853489003398199706630766239/5753669640558802076400000000000), (53818502139791/73169140000000), (-4725166002290900627300852231239/11507339281117604152800000000000)]
    bernstein := [(5907559523255326852230627277711291721/29458788559661066631168000000000000000), (1004110509949796984293909210605648073/4909798093276844438528000000000000000), (4606398582014293723456146722497958723/22094091419745799973376000000000000000), (260799495234460405026760363038985633/1227449523319211109632000000000000000), (398540679797977973427649221733186361/1841174284978816664448000000000000000)]
    reserve := (25067050497/125000000000) }

theorem quarter_033_028_valid : quarter_033_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_033_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_033_028]
  · intro i; fin_cases i <;> norm_num [quarter_033_028]
  · norm_num [quarter_033_028]
  · norm_num [quarter_033_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_033_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_033_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_033_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_033_028]

def quarter_033_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 2, 0, 2, 0, 0, 1]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (85870743/100000000), 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (19590439/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-15187964623384429949/15672351200000000000), (85870743/19590439), (-32577730683384429949/7836175600000000000), (85870743/19590439), (-49967496743384429949/15672351200000000000)]
    bernstein := [(491174581772955537851651/2507576192000000000000000), (212375570386690762474719/1003030476800000000000000), (24881778954383083676659/109421506560000000000000), (38974676531101527083863/160484876288000000000000), (16569617307944372801779/64193950515200000000000)]
    reserve := (7835049373/40000000000) }

theorem quarter_033_029_valid : quarter_033_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_033_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_033_029]
  · intro i; fin_cases i <;> norm_num [quarter_033_029]
  · norm_num [quarter_033_029]
  · norm_num [quarter_033_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_033_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_033_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_033_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_033_029]

def quarterTable033 : OwnerTable where
  mode := .quarter
  owners := ![0, 2, 0, 2, 0, 0, 1]
  rows := [quarter_033_000, quarter_033_001, quarter_033_002, quarter_033_003, quarter_033_004, quarter_033_005, quarter_033_006, quarter_033_007, quarter_033_008, quarter_033_009, quarter_033_010, quarter_033_011, quarter_033_012, quarter_033_013, quarter_033_014, quarter_033_015, quarter_033_016, quarter_033_017, quarter_033_018, quarter_033_019, quarter_033_020, quarter_033_021, quarter_033_022, quarter_033_023, quarter_033_024, quarter_033_025, quarter_033_026, quarter_033_027, quarter_033_028, quarter_033_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_033_000_valid
    · exact quarter_033_001_valid
    · exact quarter_033_002_valid
    · exact quarter_033_003_valid
    · exact quarter_033_004_valid
    · exact quarter_033_005_valid
    · exact quarter_033_006_valid
    · exact quarter_033_007_valid
    · exact quarter_033_008_valid
    · exact quarter_033_009_valid
    · exact quarter_033_010_valid
    · exact quarter_033_011_valid
    · exact quarter_033_012_valid
    · exact quarter_033_013_valid
    · exact quarter_033_014_valid
    · exact quarter_033_015_valid
    · exact quarter_033_016_valid
    · exact quarter_033_017_valid
    · exact quarter_033_018_valid
    · exact quarter_033_019_valid
    · exact quarter_033_020_valid
    · exact quarter_033_021_valid
    · exact quarter_033_022_valid
    · exact quarter_033_023_valid
    · exact quarter_033_024_valid
    · exact quarter_033_025_valid
    · exact quarter_033_026_valid
    · exact quarter_033_027_valid
    · exact quarter_033_028_valid
    · exact quarter_033_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
