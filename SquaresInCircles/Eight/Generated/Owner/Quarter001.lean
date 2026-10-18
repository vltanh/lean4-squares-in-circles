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

def quarter_001_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 0, 0, 0, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (305109/781250), (476141/781250)]
    cone := fun i => (![![0, 0, (14961777/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(305109/1562500), 0, (305109/781250), 0, 0], ![0, 0, (46788991/100000000), 0, 0]] i.1) i.2
    mu := ![(13862837/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (341629/100000000)]
    alternative := .zero
    polynomial := [(-14374691271790946411340937/1183986785368250000000000), (-9297593879616/133448828125), (-63788844655569788786860937/591993392684125000000000), (-9297593879616/133448828125), (-113202998039348631162380937/1183986785368250000000000)]
    bernstein := [(2990005041502588170728626727/4849609872868352000000000000), (7620368667567275881374279419/12124024682170880000000000000), (57200606057925900106726513837/90930185116281600000000000000), (46860259961119773118474510947/75775154263568000000000000000), (113063918489006412728021519863/189437885658920000000000000000)]
    reserve := (14920975033/25000000000) }

theorem quarter_001_000_valid : quarter_001_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_001_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_001_000]
  · intro i; fin_cases i <;> norm_num [quarter_001_000]
  · norm_num [quarter_001_000]
  · norm_num [quarter_001_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_001_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_001_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_001_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_001_000]

def quarter_001_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (37732553/100000000), (62267447/100000000)]
    cone := fun i => (![![0, 0, (1528617/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(18866277/100000000), 0, (37732553/100000000), 0, 0], ![0, 0, (4953271/10000000), 0, 0]] i.1) i.2
    mu := ![(14163403/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (354441/100000000)]
    alternative := .zero
    polynomial := [(-107611658598710606406360499/10040181445446000000000000), (-2349509744102191/35444100000000), (-181483337459563315242486833/1673363574241000000000000), (-2349509744102191/35444100000000), (-981288366158669285048560499/10040181445446000000000000)]
    bernstein := [(919532253676100215105530441101/1606429031271360000000000000000), (1879851632914358466935883430559/3212858062542720000000000000000), (3767188926728837572299399960181/6425716125085440000000000000000), (7404713308036821615973784746679/12851432250170880000000000000000), (14266927128878180023579413088861/25702864500341760000000000000000)]
    reserve := (277535741759/500000000000) }

theorem quarter_001_001_valid : quarter_001_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_001_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_001_001]
  · intro i; fin_cases i <;> norm_num [quarter_001_001]
  · norm_num [quarter_001_001]
  · norm_num [quarter_001_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_001_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_001_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_001_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_001_001]

def quarter_001_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 0, 0, 0, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (36281179/100000000), (63718821/100000000)]
    cone := fun i => (![![0, 0, (15642471/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1814059/10000000), 0, (36281179/100000000), 0, 0], ![0, 0, (6547619/12500000), 0, 0]] i.1) i.2
    mu := ![(7246767/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (367987/100000000)]
    alternative := .zero
    polynomial := [(-8328927597030419362173933/888905349343000000000000), (-2311793950369959/36798700000000), (-48640910973048999170613933/444452674671500000000000), (-2311793950369959/36798700000000), (-88952894349067578979053933/888905349343000000000000)]
    bernstein := [(1201621007407386091306135973187/2275597694318080000000000000000), (308040043995528656192395392597/568899423579520000000000000000), (77265236295115823350674097207/142224855894880000000000000000), (18976090232022837413552977017/35556213973720000000000000000), (4559949838646291704679922027/8889053493430000000000000000)]
    reserve := (128246214347/250000000000) }

theorem quarter_001_002_valid : quarter_001_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_001_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_001_002]
  · intro i; fin_cases i <;> norm_num [quarter_001_002]
  · norm_num [quarter_001_002]
  · norm_num [quarter_001_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_001_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_001_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_001_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_001_002]

def quarter_001_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (34687529/100000000), (65312471/100000000)]
    cone := fun i => (![![0, 0, (32067399/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(3468753/20000000), 0, (34687529/100000000), 0, 0], ![0, 0, (27669903/50000000), 0, 0]] i.1) i.2
    mu := ![(14856027/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (95581/25000000)]
    alternative := .zero
    polynomial := [(-22993938576098725413408389/2839907833374000000000000), (-2265528231874159/38232400000000), (-157232236230409305195663389/1419953916687000000000000), (-2265528231874159/38232400000000), (-291470533884719884977918389/2839907833374000000000000)]
    bernstein := [(13721315095064621478401170291/28399078333740000000000000000), (56494547290367897220467356867/113596313334960000000000000000), (681225850798745907422906180437/1363155760019520000000000000000), (891783001585839687797971583423/1817541013359360000000000000000), (3418956771277319837318513405851/7270164053437440000000000000000)]
    reserve := (470272300067/1000000000000) }

theorem quarter_001_003_valid : quarter_001_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_001_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_001_003]
  · intro i; fin_cases i <;> norm_num [quarter_001_003]
  · norm_num [quarter_001_003]
  · norm_num [quarter_001_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_001_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_001_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_001_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_001_003]

def quarter_001_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 0, 0, 0, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (32937947/100000000), (67062053/100000000)]
    cone := fun i => (![![0, 0, (2057901/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(8234487/50000000), 0, (32937947/100000000), 0, 0], ![0, 0, (29207921/50000000), 0, 0]] i.1) i.2
    mu := ![(3813497/25000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (79503/20000000)]
    alternative := .zero
    polynomial := [(-522976290930603728141567/75796112997750000000000), (-2208886347425191/39751500000000), (-1419268948894550494390689/12632685499625000000000), (-2208886347425191/39751500000000), (-7992637402436699238202567/75796112997750000000000)]
    bernstein := [(84874092072739102667061094153/194038049274240000000000000000), (8777224093450606029420858503/19403804927424000000000000000), (294530147709546860396101443/646793497580800000000000000), (86680303311943665214532231/194038049274240000000000000), (8277382639847301395568137/19403804927424000000000000)]
    reserve := (426585541897/1000000000000) }

theorem quarter_001_004_valid : quarter_001_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_001_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_001_004]
  · intro i; fin_cases i <;> norm_num [quarter_001_004]
  · norm_num [quarter_001_004]
  · norm_num [quarter_001_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_001_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_001_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_001_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_001_004]

def quarter_001_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (31017243/100000000), (68982757/100000000)]
    cone := fun i => (![![0, 0, (8467363/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7754311/50000000), 0, (31017243/100000000), 0, 0], ![0, 0, (30808081/50000000), 0, 0]] i.1) i.2
    mu := ![(15690873/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (41363/10000000)]
    alternative := .zero
    polynomial := [(-3751957175530520117015977/649021579899000000000000), (-2139654936678951/41363000000000), (-5299802024152296461536711/46358684278500000000000), (-2139654936678951/41363000000000), (-70445271162601630344497977/649021579899000000000000)]
    bernstein := [(64865702008638222482352647/166149524454144000000000000), (674792094324244282489899079/1661495244541440000000000000), (20424339739921842881447883077/49844857336243200000000000000), (9529763332552959388327432721/23735646350592000000000000000), (633906697069892355947829894503/1661495244541440000000000000000)]
    reserve := (381527843159/1000000000000) }

theorem quarter_001_005_valid : quarter_001_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_001_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_001_005]
  · intro i; fin_cases i <;> norm_num [quarter_001_005]
  · norm_num [quarter_001_005]
  · norm_num [quarter_001_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_001_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_001_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_001_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_001_005]

def quarter_001_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 0, 0, 0, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (7227123/25000000), (17772877/25000000)]
    cone := fun i => (![![0, 0, (6980963/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7227123/50000000), 0, (7227123/25000000), 0, 0], ![0, 0, (32474227/50000000), 0, 0]] i.1) i.2
    mu := ![(16170531/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (430747/100000000)]
    alternative := .zero
    polynomial := [(-1270666289333411194334611/267900296794500000000000), (-128446768142871/2692168750000), (-15629113707204217875794611/133950148397250000000000), (-128446768142871/2692168750000), (-29987561125075024557254611/267900296794500000000000)]
    bernstein := [(234350765761282726162670766029/685824759793920000000000000000), (30712654145497541303502871981/85728094974240000000000000000), (2913139638542120547301436363/8037008903835000000000000000), (237453987474787426860471913/669750741986250000000000000), (14008069891154608198670741/41859421374140625000000000)]
    reserve := (41830696147/125000000000) }

theorem quarter_001_006_valid : quarter_001_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_001_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_001_006]
  · intro i; fin_cases i <;> norm_num [quarter_001_006]
  · norm_num [quarter_001_006]
  · norm_num [quarter_001_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_001_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_001_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_001_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_001_006]

def quarter_001_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (13296399/50000000), (36703601/50000000)]
    cone := fun i => (![![0, 0, (7208357/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(13296399/100000000), 0, (13296399/50000000), 0, 0], ![0, 0, (68421053/100000000), 0, 0]] i.1) i.2
    mu := ![(16697261/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (448949/100000000)]
    alternative := .zero
    polynomial := [(-11364612184292589064356729/2998487451475600000000000), (-488025723632799/11223725000000), (-179091873550159228802888729/1499243725737800000000000), (-488025723632799/11223725000000), (-346819134916025868541420729/2998487451475600000000000)]
    bernstein := [(136246441847856924563076799/468513664293062500000000000), (2310367049381714429525128261/7496218628689000000000000000), (28154514575963423602974382753/89954623544268000000000000000), (292980077649934007469982920953/959515984472192000000000000000), (2190905933801913779741503162471/7676127875777536000000000000000)]
    reserve := (57083622609/200000000000) }

theorem quarter_001_007_valid : quarter_001_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_001_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_001_007]
  · intro i; fin_cases i <;> norm_num [quarter_001_007]
  · norm_num [quarter_001_007]
  · norm_num [quarter_001_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_001_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_001_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_001_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_001_007]

def quarter_001_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 0, 0, 0, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (24049023/100000000), (75950977/100000000)]
    cone := fun i => (![![0, 0, (18645369/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(187883/1562500), 0, (24049023/100000000), 0, 0], ![0, 0, (72043011/100000000), 0, 0]] i.1) i.2
    mu := ![(1727587/10000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (468331/100000000)]
    alternative := .zero
    polynomial := [(-592130163232521009777523/202270636824250000000000), (-1826546792745471/46833100000000), (-12408257453348347240388773/101135318412125000000000), (-1826546792745471/46833100000000), (-24224384743464173471000023/202270636824250000000000)]
    bernstein := [(122784263339620107957711558377/517812830270080000000000000000), (66124220278493264215192924433/258906415135040000000000000000), (101259237814788241533305556971/388359622702560000000000000000), (104431986989384370034921429/412271361680000000000000000), (7548604663746480273710102537/32363301891880000000000000000)]
    reserve := (5831145327/25000000000) }

theorem quarter_001_008_valid : quarter_001_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_001_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_001_008]
  · intro i; fin_cases i <;> norm_num [quarter_001_008]
  · norm_num [quarter_001_008]
  · norm_num [quarter_001_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_001_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_001_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_001_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_001_008]

def quarter_001_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 0, 0, 0, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (664171/3125000), (2460829/3125000)]
    cone := fun i => (![![0, 0, (3866331/10000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(664171/6250000), 0, (664171/3125000), 0, 0], ![0, 0, (4739011/6250000), 0, 0]] i.1) i.2
    mu := ![(4477937/25000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (489/100000)]
    alternative := .zero
    polynomial := [(-4733832133543288874689/2189711193000000000000), (-1634411257759/47753906250), (-46140063934181650534123/364951865500000000000), (-1634411257759/47753906250), (-272106551471546614330049/2189711193000000000000)]
    bernstein := [(63056820484380790782766031/350353790880000000000000000), (9303894629255031036217799/46713838784000000000000000), (3831329916890693390789357/18685535513600000000000000), (295623248417801293123283/1494842841088000000000000), (63657156070695807467159/358762281861120000000000)]
    reserve := (44358868873/250000000000) }

theorem quarter_001_009_valid : quarter_001_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_001_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_001_009]
  · intro i; fin_cases i <;> norm_num [quarter_001_009]
  · norm_num [quarter_001_009]
  · norm_num [quarter_001_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_001_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_001_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_001_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_001_009]

def quarter_001_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 0, 0, 0, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (18179523/100000000), (81820477/100000000)]
    cone := fun i => (![![0, 0, (40172571/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(9089761/100000000), 0, (18179523/100000000), 0, 0], ![0, 0, (79775281/100000000), 0, 0]] i.1) i.2
    mu := ![(18610951/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (511071/100000000)]
    alternative := .zero
    polynomial := [(-9525812173751588768646093/6341011559014000000000000), (-495819081164157/17035700000000), (-1243361023064464170147808279/9511517338521000000000000), (-495819081164157/17035700000000), (-144596741741627857293510487/1119002039826000000000000)]
    bernstein := [(369664029148369400685842849/3116734001486561280000000000), (2702541507450695926369574213/19479587509291008000000000000), (53006201815115764320021341327/365242265799206400000000000000), (20988043749633593264040589501/152184277416336000000000000000), (22291761804267451665470075921/190230346770420000000000000000)]
    reserve := (29295748789/250000000000) }

theorem quarter_001_010_valid : quarter_001_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_001_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_001_010]
  · intro i; fin_cases i <;> norm_num [quarter_001_010]
  · norm_num [quarter_001_010]
  · norm_num [quarter_001_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_001_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_001_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_001_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_001_010]

def quarter_001_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 1]
    lambda := ![(79218/390625), (79218/390625), (8910399/100000000), (8910399/100000000), (5364707/100000000), (5364707/100000000), (30890173/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (30420761/100000000), 0, 0]] i.1) i.2
    mu := ![(933711/10000000), (1/100000000), (2995699/50000000), (1/100000000), (1314029/50000000), (1/100000000), (193847/100000000)]
    alternative := .zero
    polynomial := [(-49972877380076132220391360114972843/178120822776815279247951750000000000), (-20099060282315321501/2322829056212000000), (-4403433208458585601460955123477229093/89060411388407639623975875000000000), (-20099060282315321501/2322829056212000000), (-8756893539537095070701518886839485343/178120822776815279247951750000000000)]
    bernstein := [(167490569969817418228630360175498141057/1781208227768152792479517500000000000000), (722190522637960391381491838259639802621/7124832911072611169918070000000000000000), (8849529938924083566226249283149314689339/85497994932871334039016840000000000000000), (11457274914743963991395949712528250150789/113997326577161778718689120000000000000000), (42125871579837813775157055210327358228817/455989306308647114874756480000000000000000)]
    reserve := (18476692763/200000000000) }

theorem quarter_001_011_valid : quarter_001_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_001_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_001_011]
  · intro i; fin_cases i <;> norm_num [quarter_001_011]
  · norm_num [quarter_001_011]
  · norm_num [quarter_001_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_001_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_001_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_001_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_001_011]

def quarter_001_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 0, 0, 0, 0, 0, 1]
    lambda := ![(5136341/25000000), (5136341/25000000), (9789321/100000000), (9789321/100000000), (4874061/100000000), (4874061/100000000), (7395627/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (14831617/50000000), 0, 0]] i.1) i.2
    mu := ![(9100819/100000000), (1/100000000), (6074539/100000000), (1/100000000), (2763207/100000000), (1/100000000), (489363/100000000)]
    alternative := .zero
    polynomial := [(-190055915588136619845512502177291/4708659235918356669837250000000000), (-9370776787737182911/3096515238184375000), (-43374686411587689041796327979837291/2354329617959178334918625000000000), (-9370776787737182911/3096515238184375000), (-86559316907587241463747143457497291/4708659235918356669837250000000000)]
    bernstein := [(1008548091581799926228441073828642178629/12054167643950993074783360000000000000000), (493622159400432919779899490870052001143/6027083821975496537391680000000000000000), (707162487072563535819064193397972946343/9040625732963244806087520000000000000000), (109447783302206413772953313771336206127/1506770955493874134347920000000000000000), (49085737087178299934455224967955709909/753385477746937067173960000000000000000)]
    reserve := (13030709653/200000000000) }

theorem quarter_001_012_valid : quarter_001_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_001_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_001_012]
  · intro i; fin_cases i <;> norm_num [quarter_001_012]
  · norm_num [quarter_001_012]
  · norm_num [quarter_001_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_001_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_001_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_001_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_001_012]

def quarter_001_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 1]
    lambda := ![(19615287/100000000), (19615287/100000000), (363767/3125000), (363767/3125000), (388679/6250000), (388679/6250000), (25050609/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2611437/10000000), 0, 0]] i.1) i.2
    mu := ![(2009851/25000000), (1/100000000), (3005231/50000000), (1/100000000), (3334769/100000000), (1/100000000), (128523/10000000)]
    alternative := .zero
    polynomial := [(39144780692292322374011743676175149/2588739392411655335014647000000000000), (-39414052433159386713/32186775317750000000), (-7056973570829286650842766252660399851/1294369696205827667507323500000000000), (-39414052433159386713/32186775317750000000), (-14153091922350865624059544248996974851/2588739392411655335014647000000000000)]
    bernstein := [(26026990535470511548069523102070358264349/414198302785864853602343520000000000000000), (99188822088747004584110781372284235141/1694062588081246844999360000000000000000), (266945973476448787091034185713934350690247/4970379633430378243228122240000000000000000), (53355388737859627620589090066481895947583/1104528807428972942939582720000000000000000), (280622228282303358263293753620219679501949/6627172844573837657637496320000000000000000)]
    reserve := (21172092147/500000000000) }

theorem quarter_001_013_valid : quarter_001_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_001_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_001_013]
  · intro i; fin_cases i <;> norm_num [quarter_001_013]
  · norm_num [quarter_001_013]
  · norm_num [quarter_001_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_001_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_001_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_001_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_001_013]

def quarter_001_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 0, 0, 0, 0, 0, 1]
    lambda := ![(18729129/100000000), (18729129/100000000), (6594247/50000000), (6594247/50000000), (7457531/100000000), (7457531/100000000), (21249693/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (23051907/100000000), 0, 0]] i.1) i.2
    mu := ![(7157269/100000000), (1/100000000), (118453/2000000), (1/100000000), (3828341/100000000), (1/100000000), (1938613/100000000)]
    alternative := .zero
    polynomial := [(148588343486133153007999534874029039/6292093096403403891267281000000000000), (-222448597178532809253/287043157111250000000), (-8979251094774955588639159048811395961/3146046548201701945633640500000000000), (-222448597178532809253/287043157111250000000), (-18107090533036044330286317632496820961/6292093096403403891267281000000000000)]
    bernstein := [(663903494544280695675846385488092564327839/16107758326792713961644239360000000000000000), (46884657719389982287442230705810085203/1258418619280680778253456200000000000000), (996814172229787899558699743403748967239/30202046862736338678082948800000000000000), (1398940000047202139962350805540283/49156977315651592900525632812500000), (148588343486133153007999534874029039/6292093096403403891267281000000000000)]
    reserve := (23615089797/1000000000000) }

theorem quarter_001_014_valid : quarter_001_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_001_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_001_014]
  · intro i; fin_cases i <;> norm_num [quarter_001_014]
  · norm_num [quarter_001_014]
  · norm_num [quarter_001_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_001_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_001_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_001_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_001_014]

def quarter_001_015 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 1]
    lambda := ![(9109861/50000000), (9109861/50000000), (14180267/100000000), (14180267/100000000), (8190843/100000000), (8190843/100000000), (588073/3125000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (33719/160000), 0, 0]] i.1) i.2
    mu := ![(6618519/100000000), (1/100000000), (291689/5000000), (1/100000000), (4137861/100000000), (1/100000000), (95123/4000000)]
    alternative := .zero
    polynomial := [(64752068404109653647110560539097/2783425878978341040801000000000000), (23733312235424505961/138731663735000000000), (-2763299689012910119731159288680903/1391712939489170520400500000000000), (23733312235424505961/138731663735000000000), (-5591351446429929893109429137900903/2783425878978341040801000000000000)]
    bernstein := [(64752068404109653647110560539097/2783425878978341040801000000000000), (270912534275371357330207390112203/11133703515913364163204000000000000), (336616854232152009966635886392940697/13360444219096036995844800000000000000), (460512394453786240765797425631365003/17813925625461382661126400000000000000), (26773014123165012118696545547255319071/1017938607169221866350080000000000000000)]
    reserve := (4652688537/200000000000) }

theorem quarter_001_015_valid : quarter_001_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_001_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_001_015]
  · intro i; fin_cases i <;> norm_num [quarter_001_015]
  · norm_num [quarter_001_015]
  · norm_num [quarter_001_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_001_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_001_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_001_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_001_015]

def quarter_001_016 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 0, 0, 0, 0, 0, 1]
    lambda := ![(5548063/25000000), (5548063/25000000), (3554337/20000000), (3554337/20000000), (10036063/100000000), (10036063/100000000), 0]
    cone := fun i => (![![0, 0, 0, (5548063/50000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2620963/100000000), 0, 0]] i.1) i.2
    mu := ![(3965129/100000000), (1/100000000), (87583/1250000), (1/100000000), (4029/78125), (1/100000000), (2620963/100000000)]
    alternative := .zero
    polynomial := [(309720478045901452011391851199247/23470117811261342821689600000000000), (19719685599231/35033200000000), (-4898827211326100125561874838592753/11735058905630671410844800000000000), (19719685599231/35033200000000), (-10107374900698101703135141528384753/23470117811261342821689600000000000)]
    bernstein := [(1623230032270893903117262607365669845647/60083501596829037623525376000000000000000), (304525668656668513714372825116047349349/10013916932804839603920896000000000000000), (217362792454199358532880516405913127163/6437518028231682602520576000000000000000), (92835341154960229802264218468446850549/2503479233201209900980224000000000000000), (151578267597204231943877382157356292847/3755218849801814851470336000000000000000)]
    reserve := (27016235557/1000000000000) }

theorem quarter_001_016_valid : quarter_001_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_001_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_001_016]
  · intro i; fin_cases i <;> norm_num [quarter_001_016]
  · norm_num [quarter_001_016]
  · norm_num [quarter_001_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_001_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_001_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_001_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_001_016]

def quarter_001_017 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 1]
    lambda := ![(11115623/50000000), (11115623/50000000), (1797751/10000000), (1797751/10000000), (2447811/25000000), (2447811/25000000), 0]
    cone := fun i => (![![0, 0, 0, (11115623/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2557027/100000000), 0, 0]] i.1) i.2
    mu := ![(15516/390625), (1/100000000), (1715721/25000000), (1/100000000), (5172597/100000000), (1/100000000), (639257/25000000)]
    alternative := .zero
    polynomial := [(431595950602956554389227780520411/34775672182001549328768000000000000), (19983122363873/34314420000000), (-7299469280331375600700535068759589/17387836091000774664384000000000000), (19983122363873/34314420000000), (-15030534511265707755790297918039589/34775672182001549328768000000000000)]
    bernstein := [(32231379184124965744991432396274864173/794872507017178270371840000000000000000), (69873104958676372933948407058330603319/1589745014034356540743680000000000000000), (3159547637772155016400487837066400133897/66769290589442974711234560000000000000000), (751599307154299571892116276729666647699/14837620130987327713607680000000000000000), (4803648281112949702264534907366150790091/89025720785923966281646080000000000000000)]
    reserve := (2534319883/62500000000) }

theorem quarter_001_017_valid : quarter_001_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_001_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_001_017]
  · intro i; fin_cases i <;> norm_num [quarter_001_017]
  · norm_num [quarter_001_017]
  · norm_num [quarter_001_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_001_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_001_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_001_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_001_017]

def quarter_001_018 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 0, 0, 0, 0, 0, 1]
    lambda := ![0, (28883937/100000000), (11691303/50000000), (11691303/50000000), (6087713/50000000), (6087713/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1444197/100000000), 0, (28883937/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3179667/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (271193/3125000), (1/100000000), (1332261/20000000), (1/100000000), (3179667/100000000)]
    alternative := .zero
    polynomial := [(23353711259853437449450813/3063501956249692776000000000000), (25976219946147/33377600000000), (-884836621325668970675941669187/1531750978124846388000000000000), (25976219946147/33377600000000), (-1769696596362597794789332789187/3063501956249692776000000000000)]
    bernstein := [(434770586537529962059560478955370253/7842565007999213506560000000000000000), (9024349898955219215470226060454127/150818557846138721280000000000000000), (94390690051763935774752425319791851/1470480938999852532480000000000000000), (645723047881283453974427366543003/9426159865383670080000000000000000), (2229518142347752586700267257453413/30635019562496927760000000000000000)]
    reserve := (5543729457/100000000000) }

theorem quarter_001_018_valid : quarter_001_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_001_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_001_018]
  · intro i; fin_cases i <;> norm_num [quarter_001_018]
  · norm_num [quarter_001_018]
  · norm_num [quarter_001_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_001_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_001_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_001_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_001_018]

def quarter_001_019 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 0, 0, 0, 0, 0, 1]
    lambda := ![0, (2917131/10000000), (591473/2500000), (591473/2500000), (470217/4000000), (470217/4000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(291713/20000000), 0, (2917131/10000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1534991/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (2130411/25000000), (1/100000000), (3337707/50000000), (1/100000000), (1534991/50000000)]
    alternative := .zero
    polynomial := [(-10165827135246403862977721791/3638280544980442269000000000000), (575134741321/710137000000), (-1071499923581180657524001621791/1819140272490221134500000000000), (575134741321/710137000000), (-2132834020027114911185025521791/3638280544980442269000000000000)]
    bernstein := [(2657991772079360147490979202210009/36382805449804422690000000000000000), (752095870730493127212643296575943/9702081453281179384000000000000000), (5724062366367131129150561079100583/69854986463624491564800000000000000), (107207422310162732515649058391359/1241866426019990961152000000000000), (54052665173115805169470162337321/596095884489595661352960000000000)]
    reserve := (73056262133/1000000000000) }

theorem quarter_001_019_valid : quarter_001_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_001_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_001_019]
  · intro i; fin_cases i <;> norm_num [quarter_001_019]
  · norm_num [quarter_001_019]
  · norm_num [quarter_001_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_001_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_001_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_001_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_001_019]

def quarter_001_020 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 0, 0, 0, 0, 0, 1]
    lambda := ![0, (29403767/100000000), (5986759/25000000), (5986759/25000000), (283777/2500000), (283777/2500000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(367547/25000000), 0, (29403767/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (592877/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1043449/12500000), (1/100000000), (1339259/20000000), (1/100000000), (1482193/50000000)]
    alternative := .zero
    polynomial := [(-163236846514029021827870732147/24855459979594441956000000000000), (6070112645557/7196200000000), (-7471678385692226279520353252147/12427729989797220978000000000000), (6070112645557/7196200000000), (-14780119924870423537212835772147/24855459979594441956000000000000)]
    bernstein := [(370501624698396943069232310891157/4072318563056753370071040000000000), (4862917792570204399018671630592507/50903982038209417125888000000000000), (190978463884896697089019338887324719/1908899326432853142220800000000000000), (166278207788574082620061838987815951/1590749438694044285184000000000000000), (433394172875697418163693283939877693/3976873596735110712960000000000000000)]
    reserve := (18196102243/200000000000) }

theorem quarter_001_020_valid : quarter_001_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_001_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_001_020]
  · intro i; fin_cases i <;> norm_num [quarter_001_020]
  · norm_num [quarter_001_020]
  · norm_num [quarter_001_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_001_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_001_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_001_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_001_020]

def quarter_001_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 1]
    lambda := ![0, (5918093/20000000), (6061129/25000000), (6061129/25000000), (10960251/100000000), (10960251/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1479523/100000000), 0, (5918093/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2862319/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (8158161/100000000), (1/100000000), (1344603/20000000), (1/100000000), (2862319/100000000)]
    alternative := .zero
    polynomial := [(-159530593894410350119531927853/13954743654062852212000000000000), (35870325106997/40790805000000), (-4288804130689599711913117727853/6977371827031426106000000000000), (35870325106997/40790805000000), (-8418077667484789073706703527853/13954743654062852212000000000000)]
    bernstein := [(244054552709370112854476200709222307/2232758984650056353920000000000000000), (1526804216540542605177499579693306949/13396553907900338123520000000000000000), (3177723851902012459349833029608166881/26793107815800676247040000000000000000), (6602110086585035726388652752590902589/53586215631601352494080000000000000000), (13694599392046582281011137106163783641/107172431263202704988160000000000000000)]
    reserve := (109306268337/1000000000000) }

theorem quarter_001_021_valid : quarter_001_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_001_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_001_021]
  · intro i; fin_cases i <;> norm_num [quarter_001_021]
  · norm_num [quarter_001_021]
  · norm_num [quarter_001_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_001_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_001_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_001_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_001_021]

def quarter_001_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 0, 0, 0, 0, 0, 1]
    lambda := ![0, (29739637/100000000), (196393/800000), (196393/800000), (165329/1562500), (165329/1562500), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(743491/50000000), 0, (29739637/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (276329/10000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1591069/20000000), (1/100000000), (6754729/100000000), (1/100000000), (2763291/100000000)]
    alternative := .zero
    polynomial := [(-693813447920694318220290107357/39597001777056020788000000000000), (5840656529341/6364276000000), (-12469818039300704187216029667357/19798500888528010394000000000000), (5840656529341/6364276000000), (-24245822630680714056211769227357/39597001777056020788000000000000)]
    bernstein := [(764051527550954973660109768480565779/5962842620544906659840000000000000000), (99086345093659596594132361827648797/745355327568113332480000000000000000), (54530698302843476127298832652562983/395970017770560207880000000000000000), (14102946423482668421730137309182313/98992504442640051970000000000000000), (910680387828331655160383180076667/6187031527665003248125000000000000)]
    reserve := (128135450853/1000000000000) }

theorem quarter_001_022_valid : quarter_001_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_001_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_001_022]
  · intro i; fin_cases i <;> norm_num [quarter_001_022]
  · norm_num [quarter_001_022]
  · norm_num [quarter_001_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_001_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_001_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_001_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_001_022]

def quarter_001_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 1]
    lambda := ![0, (3732323/12500000), (24858847/100000000), (24858847/100000000), (10211861/100000000), (10211861/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1492929/100000000), 0, (3732323/12500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2666873/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (3870493/50000000), (1/100000000), (271627/4000000), (1/100000000), (1333437/50000000)]
    alternative := .zero
    polynomial := [(-17513741817570612647708274119/700941428699842753500000000000), (92781246411581/96762325000000), (-226804927096713269069418714119/350470714349921376750000000000), (92781246411581/96762325000000), (-436096112375855925491129154119/700941428699842753500000000000)]
    bernstein := [(16162729814832018789541338303889/109522098234350430234375000000000), (267312364556601006654502261008677/1752353571749606883750000000000000), (473109744940763685266697373106461/3004034694427897515000000000000000), (36430309570028747965884224076200849/224301257183949681120000000000000000), (300245424214740438465522268416340441/1794410057471597448960000000000000000)]
    reserve := (36893764079/250000000000) }

theorem quarter_001_023_valid : quarter_001_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_001_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_001_023]
  · intro i; fin_cases i <;> norm_num [quarter_001_023]
  · norm_num [quarter_001_023]
  · norm_num [quarter_001_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_001_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_001_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_001_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_001_023]

def quarter_001_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 0, 0, 0, 0, 0, 1]
    lambda := ![0, (29953703/100000000), (25171881/100000000), (25171881/100000000), (9851267/100000000), (9851267/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(299537/20000000), 0, (29953703/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2572703/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (7516771/100000000), (1/100000000), (273207/4000000), (1/100000000), (2572703/100000000)]
    alternative := .zero
    polynomial := [(-14084687125850369313817804177/414383648803534564000000000000), (753991047425343/751677100000000), (-138207934569024166116722724177/207191824401767282000000000000), (753991047425343/751677100000000), (-262331182012197962919627644177/414383648803534564000000000000)]
    bernstein := [(177938918688241401901710897165956303/1060822140937048483840000000000000000), (1078929914764748853306389237981191/6240130240806167552000000000000000), (1888771112778063434803200688371759/10608221409370484838400000000000000), (194317791603790014940382465679479/1060822140937048483840000000000000), (1174950939817222382519295968991/6240130240806167552000000000000)]
    reserve := (83868403487/500000000000) }

theorem quarter_001_024_valid : quarter_001_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_001_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_001_024]
  · intro i; fin_cases i <;> norm_num [quarter_001_024]
  · norm_num [quarter_001_024]
  · norm_num [quarter_001_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_001_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_001_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_001_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_001_024]

def quarter_001_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 1]
    lambda := ![0, (15015269/50000000), (25486643/100000000), (25486643/100000000), (9498089/100000000), (9498089/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1501527/100000000), 0, (15015269/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (620117/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (7284229/100000000), (1/100000000), (687263/10000000), (1/100000000), (2480469/100000000)]
    alternative := .zero
    polynomial := [(-555262639442624994516519953971/12417676965487241463000000000000), (382688800551967/364211450000000), (-4284357839280517927214490893971/6208838482743620731500000000000), (382688800551967/364211450000000), (-8013453039118410859912461833971/12417676965487241463000000000000)]
    bernstein := [(599980504385136028529676907982381/3178925303164733814528000000000000), (108265742797133013719910692847479/557706193537672599040000000000000), (190260384905282832168334270449738431/953677590949420144358400000000000000), (11425354137025961287937658059947727/55770619353767259904000000000000000), (6682506751804553027263015263672699389/31789253031647338145280000000000000000)]
    reserve := (188736899161/1000000000000) }

theorem quarter_001_025_valid : quarter_001_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_001_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_001_025]
  · intro i; fin_cases i <;> norm_num [quarter_001_025]
  · norm_num [quarter_001_025]
  · norm_num [quarter_001_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_001_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_001_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_001_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_001_025]

def quarter_001_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 0, 0, 0, 0, 0, 1]
    lambda := ![0, (6018769/20000000), (25801747/100000000), (25801747/100000000), (915133/10000000), (915133/10000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(376173/25000000), 0, (6018769/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2389911/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (880593/12500000), (1/100000000), (3458757/50000000), (1/100000000), (2389911/100000000)]
    alternative := .zero
    polynomial := [(-185594548897684243768286516783/3235150507796591916000000000000), (155294754989443/140894880000000), (-1159175728230703530251856716783/1617575253898295958000000000000), (155294754989443/140894880000000), (-2132756907563722816735426916783/3235150507796591916000000000000)]
    bernstein := [(581660042222744045279862603102507499/2760661766653091768320000000000000000), (149311370087734301286761537122721127/690165441663272942080000000000000000), (344700176089700084829463336182763039/1552872243742364119680000000000000000), (29452903414749209814012769972655249/129406020311863676640000000000000000), (7544926344107428750181998407451177/32351505077965919160000000000000000)]
    reserve := (210695873449/1000000000000) }

theorem quarter_001_026_valid : quarter_001_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_001_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_001_026]
  · intro i; fin_cases i <;> norm_num [quarter_001_026]
  · norm_num [quarter_001_026]
  · norm_num [quarter_001_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_001_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_001_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_001_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_001_026]

def quarter_001_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 1]
    lambda := ![0, (15073833/50000000), (13058001/50000000), (13058001/50000000), (1762033/20000000), (1762033/20000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1507383/100000000), 0, (15073833/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1150407/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (6799557/100000000), (1/100000000), (696437/10000000), (1/100000000), (1150407/50000000)]
    alternative := .zero
    polynomial := [(-1541939612754997933748030947/21363568131934362600000000000), (65611375462611/56662975000000), (-7982556778853008909624946947/10681784065967181300000000000), (65611375462611/56662975000000), (-14423173944951019885501862947/21363568131934362600000000000)]
    bernstein := [(49934930947319711472292168646693/213635681319343626000000000000000), (204809646661957858730705610583103/854542725277374504000000000000000), (359782904968604270743174366411277/1464930386189784864000000000000000), (56375613998090372665756079561743/224142354171114624000000000000000), (230805595884299472499030019835953/896569416684458496000000000000000)]
    reserve := (233738721167/1000000000000) }

theorem quarter_001_027_valid : quarter_001_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_001_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_001_027]
  · intro i; fin_cases i <;> norm_num [quarter_001_027]
  · norm_num [quarter_001_027]
  · norm_num [quarter_001_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_001_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_001_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_001_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_001_027]

def quarter_001_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 0, 0, 0, 0, 0, 1]
    lambda := ![0, (30195401/100000000), (6607097/25000000), (6607097/25000000), (1059239/12500000), (1059239/12500000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(150977/10000000), 0, (30195401/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2213/100000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (3274889/50000000), (1/100000000), (7012801/100000000), (1/100000000), (2213001/100000000)]
    alternative := .zero
    polynomial := [(-18174190912367543131803592456249/203296406112975244356000000000000), (199503943360897/163744450000000), (-79560355956768931195827660016249/101648203056487622178000000000000), (199503943360897/163744450000000), (-140946521001170319259851727576249/203296406112975244356000000000000)]
    bernstein := [(134270547016186968505767755009538653111/520438799649216625551360000000000000000), (848919345627624874485994064507770709/3212585183019855713280000000000000000), (105583101842481753648088152322310703293/390329099736912469163520000000000000000), (222266662100678749578300958392506189/803146295754963928320000000000000000), (9204963839318639919568000282166225351/32527424978076039096960000000000000000)]
    reserve := (1289974413/5000000000) }

theorem quarter_001_028_valid : quarter_001_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_001_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_001_028]
  · intro i; fin_cases i <;> norm_num [quarter_001_028]
  · norm_num [quarter_001_028]
  · norm_num [quarter_001_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_001_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_001_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_001_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_001_028]

def quarter_001_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 0, 0, 0, 0, 0, 1]
    lambda := ![0, (7559971/25000000), (5347609/20000000), (5347609/20000000), (2035503/25000000), (2035503/25000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(755997/50000000), 0, (7559971/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2126323/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (15741/250000), (1/100000000), (110351/1562500), (1/100000000), (2126323/100000000)]
    alternative := .zero
    polynomial := [(-6460682003404520594859143923/59095962652806288000000000000), (40427768959339/31482000000000), (-24331232558296464830765063923/29547981326403144000000000000), (40427768959339/31482000000000), (-42201783113188409066670983923/59095962652806288000000000000)]
    bernstein := [(99315686655200965124614642277751/350198297201815040000000000000000), (3695622310549625261077540240329/12734483534611456000000000000000), (1347108300080161062675308375817023/4538569931735522918400000000000000), (183613582215573400729987237769401/605142657564736389120000000000000), (75045560896047120766540292306333/242057063025894555648000000000000)]
    reserve := (283598428229/1000000000000) }

theorem quarter_001_029_valid : quarter_001_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_001_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_001_029]
  · intro i; fin_cases i <;> norm_num [quarter_001_029]
  · norm_num [quarter_001_029]
  · norm_num [quarter_001_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_001_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_001_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_001_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_001_029]

def quarterTable001 : OwnerTable where
  mode := .quarter
  owners := ![0, 0, 0, 0, 0, 0, 1]
  rows := [quarter_001_000, quarter_001_001, quarter_001_002, quarter_001_003, quarter_001_004, quarter_001_005, quarter_001_006, quarter_001_007, quarter_001_008, quarter_001_009, quarter_001_010, quarter_001_011, quarter_001_012, quarter_001_013, quarter_001_014, quarter_001_015, quarter_001_016, quarter_001_017, quarter_001_018, quarter_001_019, quarter_001_020, quarter_001_021, quarter_001_022, quarter_001_023, quarter_001_024, quarter_001_025, quarter_001_026, quarter_001_027, quarter_001_028, quarter_001_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_001_000_valid
    · exact quarter_001_001_valid
    · exact quarter_001_002_valid
    · exact quarter_001_003_valid
    · exact quarter_001_004_valid
    · exact quarter_001_005_valid
    · exact quarter_001_006_valid
    · exact quarter_001_007_valid
    · exact quarter_001_008_valid
    · exact quarter_001_009_valid
    · exact quarter_001_010_valid
    · exact quarter_001_011_valid
    · exact quarter_001_012_valid
    · exact quarter_001_013_valid
    · exact quarter_001_014_valid
    · exact quarter_001_015_valid
    · exact quarter_001_016_valid
    · exact quarter_001_017_valid
    · exact quarter_001_018_valid
    · exact quarter_001_019_valid
    · exact quarter_001_020_valid
    · exact quarter_001_021_valid
    · exact quarter_001_022_valid
    · exact quarter_001_023_valid
    · exact quarter_001_024_valid
    · exact quarter_001_025_valid
    · exact quarter_001_026_valid
    · exact quarter_001_027_valid
    · exact quarter_001_028_valid
    · exact quarter_001_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
