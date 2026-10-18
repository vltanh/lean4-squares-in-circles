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

def quarter_021_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 1, 0, 2, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (305109/781250), (476141/781250)]
    cone := fun i => (![![0, 0, (14961777/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(305109/1562500), 0, (305109/781250), 0, 0], ![0, 0, (46788991/100000000), 0, 0]] i.1) i.2
    mu := ![(13862837/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (341629/100000000)]
    alternative := .zero
    polynomial := [(-14374691271790946411340937/1183986785368250000000000), (-9297593879616/133448828125), (-63788844655569788786860937/591993392684125000000000), (-9297593879616/133448828125), (-113202998039348631162380937/1183986785368250000000000)]
    bernstein := [(2990005041502588170728626727/4849609872868352000000000000), (7620368667567275881374279419/12124024682170880000000000000), (57200606057925900106726513837/90930185116281600000000000000), (46860259961119773118474510947/75775154263568000000000000000), (113063918489006412728021519863/189437885658920000000000000000)]
    reserve := (14920975033/25000000000) }

theorem quarter_021_000_valid : quarter_021_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_021_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_021_000]
  · intro i; fin_cases i <;> norm_num [quarter_021_000]
  · norm_num [quarter_021_000]
  · norm_num [quarter_021_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_021_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_021_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_021_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_021_000]

def quarter_021_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (37732553/100000000), (62267447/100000000)]
    cone := fun i => (![![0, 0, (1528617/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(18866277/100000000), 0, (37732553/100000000), 0, 0], ![0, 0, (4953271/10000000), 0, 0]] i.1) i.2
    mu := ![(14163403/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (354441/100000000)]
    alternative := .zero
    polynomial := [(-107611658598710606406360499/10040181445446000000000000), (-2349509744102191/35444100000000), (-181483337459563315242486833/1673363574241000000000000), (-2349509744102191/35444100000000), (-981288366158669285048560499/10040181445446000000000000)]
    bernstein := [(919532253676100215105530441101/1606429031271360000000000000000), (1879851632914358466935883430559/3212858062542720000000000000000), (3767188926728837572299399960181/6425716125085440000000000000000), (7404713308036821615973784746679/12851432250170880000000000000000), (14266927128878180023579413088861/25702864500341760000000000000000)]
    reserve := (277535741759/500000000000) }

theorem quarter_021_001_valid : quarter_021_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_021_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_021_001]
  · intro i; fin_cases i <;> norm_num [quarter_021_001]
  · norm_num [quarter_021_001]
  · norm_num [quarter_021_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_021_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_021_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_021_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_021_001]

def quarter_021_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 1, 0, 2, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (36281179/100000000), (63718821/100000000)]
    cone := fun i => (![![0, 0, (15642471/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1814059/10000000), 0, (36281179/100000000), 0, 0], ![0, 0, (6547619/12500000), 0, 0]] i.1) i.2
    mu := ![(7246767/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (367987/100000000)]
    alternative := .zero
    polynomial := [(-8328927597030419362173933/888905349343000000000000), (-2311793950369959/36798700000000), (-48640910973048999170613933/444452674671500000000000), (-2311793950369959/36798700000000), (-88952894349067578979053933/888905349343000000000000)]
    bernstein := [(1201621007407386091306135973187/2275597694318080000000000000000), (308040043995528656192395392597/568899423579520000000000000000), (77265236295115823350674097207/142224855894880000000000000000), (18976090232022837413552977017/35556213973720000000000000000), (4559949838646291704679922027/8889053493430000000000000000)]
    reserve := (128246214347/250000000000) }

theorem quarter_021_002_valid : quarter_021_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_021_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_021_002]
  · intro i; fin_cases i <;> norm_num [quarter_021_002]
  · norm_num [quarter_021_002]
  · norm_num [quarter_021_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_021_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_021_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_021_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_021_002]

def quarter_021_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (34687529/100000000), (65312471/100000000)]
    cone := fun i => (![![0, 0, (32067399/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(3468753/20000000), 0, (34687529/100000000), 0, 0], ![0, 0, (27669903/50000000), 0, 0]] i.1) i.2
    mu := ![(14856027/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (95581/25000000)]
    alternative := .zero
    polynomial := [(-22993938576098725413408389/2839907833374000000000000), (-2265528231874159/38232400000000), (-157232236230409305195663389/1419953916687000000000000), (-2265528231874159/38232400000000), (-291470533884719884977918389/2839907833374000000000000)]
    bernstein := [(13721315095064621478401170291/28399078333740000000000000000), (56494547290367897220467356867/113596313334960000000000000000), (681225850798745907422906180437/1363155760019520000000000000000), (891783001585839687797971583423/1817541013359360000000000000000), (3418956771277319837318513405851/7270164053437440000000000000000)]
    reserve := (470272300067/1000000000000) }

theorem quarter_021_003_valid : quarter_021_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_021_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_021_003]
  · intro i; fin_cases i <;> norm_num [quarter_021_003]
  · norm_num [quarter_021_003]
  · norm_num [quarter_021_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_021_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_021_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_021_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_021_003]

def quarter_021_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 1, 0, 2, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (32937947/100000000), (67062053/100000000)]
    cone := fun i => (![![0, 0, (2057901/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(8234487/50000000), 0, (32937947/100000000), 0, 0], ![0, 0, (29207921/50000000), 0, 0]] i.1) i.2
    mu := ![(3813497/25000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (79503/20000000)]
    alternative := .zero
    polynomial := [(-522976290930603728141567/75796112997750000000000), (-2208886347425191/39751500000000), (-1419268948894550494390689/12632685499625000000000), (-2208886347425191/39751500000000), (-7992637402436699238202567/75796112997750000000000)]
    bernstein := [(84874092072739102667061094153/194038049274240000000000000000), (8777224093450606029420858503/19403804927424000000000000000), (294530147709546860396101443/646793497580800000000000000), (86680303311943665214532231/194038049274240000000000000), (8277382639847301395568137/19403804927424000000000000)]
    reserve := (426585541897/1000000000000) }

theorem quarter_021_004_valid : quarter_021_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_021_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_021_004]
  · intro i; fin_cases i <;> norm_num [quarter_021_004]
  · norm_num [quarter_021_004]
  · norm_num [quarter_021_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_021_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_021_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_021_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_021_004]

def quarter_021_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (31017243/100000000), (68982757/100000000)]
    cone := fun i => (![![0, 0, (8467363/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7754311/50000000), 0, (31017243/100000000), 0, 0], ![0, 0, (30808081/50000000), 0, 0]] i.1) i.2
    mu := ![(15690873/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (41363/10000000)]
    alternative := .zero
    polynomial := [(-3751957175530520117015977/649021579899000000000000), (-2139654936678951/41363000000000), (-5299802024152296461536711/46358684278500000000000), (-2139654936678951/41363000000000), (-70445271162601630344497977/649021579899000000000000)]
    bernstein := [(64865702008638222482352647/166149524454144000000000000), (674792094324244282489899079/1661495244541440000000000000), (20424339739921842881447883077/49844857336243200000000000000), (9529763332552959388327432721/23735646350592000000000000000), (633906697069892355947829894503/1661495244541440000000000000000)]
    reserve := (381527843159/1000000000000) }

theorem quarter_021_005_valid : quarter_021_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_021_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_021_005]
  · intro i; fin_cases i <;> norm_num [quarter_021_005]
  · norm_num [quarter_021_005]
  · norm_num [quarter_021_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_021_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_021_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_021_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_021_005]

def quarter_021_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 1, 0, 2, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (7227123/25000000), (71091509/100000000)]
    cone := fun i => (![![0, 0, (2181551/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7227123/50000000), 0, (7227123/25000000), 0, 0], ![0, 0, (32474227/50000000), 0, 0]] i.1) i.2
    mu := ![(16170531/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (430747/100000000)]
    alternative := .zero
    polynomial := [(-33037324067310910181975111/6965407716657000000000000), (-513787079798607/10768675000000), (-406356962183206827945305111/3482703858328500000000000), (-513787079798607/10768675000000), (-779676600299102745708635111/6965407716657000000000000)]
    bernstein := [(6093119769647584902599704905529/17831443754641920000000000000000), (798528990934761674562500137481/2228930469330240000000000000000), (75741629048545712115187705363/208962231499710000000000000000), (474907964925119125600886801/1339501483972500000000000000), (28016139137347074902693557/83718842748281250000000000)]
    reserve := (2614418449/7812500000) }

theorem quarter_021_006_valid : quarter_021_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_021_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_021_006]
  · intro i; fin_cases i <;> norm_num [quarter_021_006]
  · norm_num [quarter_021_006]
  · norm_num [quarter_021_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_021_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_021_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_021_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_021_006]

def quarter_021_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (13296399/50000000), (36703601/50000000)]
    cone := fun i => (![![0, 0, (7208357/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(13296399/100000000), 0, (13296399/50000000), 0, 0], ![0, 0, (68421053/100000000), 0, 0]] i.1) i.2
    mu := ![(16697261/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (448949/100000000)]
    alternative := .zero
    polynomial := [(-11364612184292589064356729/2998487451475600000000000), (-488025723632799/11223725000000), (-179091873550159228802888729/1499243725737800000000000), (-488025723632799/11223725000000), (-346819134916025868541420729/2998487451475600000000000)]
    bernstein := [(136246441847856924563076799/468513664293062500000000000), (2310367049381714429525128261/7496218628689000000000000000), (28154514575963423602974382753/89954623544268000000000000000), (292980077649934007469982920953/959515984472192000000000000000), (2190905933801913779741503162471/7676127875777536000000000000000)]
    reserve := (57083622609/200000000000) }

theorem quarter_021_007_valid : quarter_021_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_021_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_021_007]
  · intro i; fin_cases i <;> norm_num [quarter_021_007]
  · norm_num [quarter_021_007]
  · norm_num [quarter_021_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_021_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_021_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_021_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_021_007]

def quarter_021_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 1, 0, 2, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (24049023/100000000), (75950977/100000000)]
    cone := fun i => (![![0, 0, (18645369/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(187883/1562500), 0, (24049023/100000000), 0, 0], ![0, 0, (72043011/100000000), 0, 0]] i.1) i.2
    mu := ![(1727587/10000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (468331/100000000)]
    alternative := .zero
    polynomial := [(-592130163232521009777523/202270636824250000000000), (-1826546792745471/46833100000000), (-12408257453348347240388773/101135318412125000000000), (-1826546792745471/46833100000000), (-24224384743464173471000023/202270636824250000000000)]
    bernstein := [(122784263339620107957711558377/517812830270080000000000000000), (66124220278493264215192924433/258906415135040000000000000000), (101259237814788241533305556971/388359622702560000000000000000), (104431986989384370034921429/412271361680000000000000000), (7548604663746480273710102537/32363301891880000000000000000)]
    reserve := (5831145327/25000000000) }

theorem quarter_021_008_valid : quarter_021_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_021_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_021_008]
  · intro i; fin_cases i <;> norm_num [quarter_021_008]
  · norm_num [quarter_021_008]
  · norm_num [quarter_021_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_021_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_021_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_021_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_021_008]

def quarter_021_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 1, 0, 2, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (664171/3125000), (2460829/3125000)]
    cone := fun i => (![![0, 0, (3866331/10000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(664171/6250000), 0, (664171/3125000), 0, 0], ![0, 0, (4739011/6250000), 0, 0]] i.1) i.2
    mu := ![(4477937/25000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (489/100000)]
    alternative := .zero
    polynomial := [(-4733832133543288874689/2189711193000000000000), (-1634411257759/47753906250), (-46140063934181650534123/364951865500000000000), (-1634411257759/47753906250), (-272106551471546614330049/2189711193000000000000)]
    bernstein := [(63056820484380790782766031/350353790880000000000000000), (9303894629255031036217799/46713838784000000000000000), (3831329916890693390789357/18685535513600000000000000), (295623248417801293123283/1494842841088000000000000), (63657156070695807467159/358762281861120000000000)]
    reserve := (44358868873/250000000000) }

theorem quarter_021_009_valid : quarter_021_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_021_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_021_009]
  · intro i; fin_cases i <;> norm_num [quarter_021_009]
  · norm_num [quarter_021_009]
  · norm_num [quarter_021_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_021_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_021_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_021_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_021_009]

def quarter_021_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 1, 0, 2, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (18179523/100000000), (81820477/100000000)]
    cone := fun i => (![![0, 0, (40172571/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(9089761/100000000), 0, (18179523/100000000), 0, 0], ![0, 0, (79775281/100000000), 0, 0]] i.1) i.2
    mu := ![(18610951/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (511071/100000000)]
    alternative := .zero
    polynomial := [(-9525812173751588768646093/6341011559014000000000000), (-495819081164157/17035700000000), (-1243361023064464170147808279/9511517338521000000000000), (-495819081164157/17035700000000), (-144596741741627857293510487/1119002039826000000000000)]
    bernstein := [(369664029148369400685842849/3116734001486561280000000000), (2702541507450695926369574213/19479587509291008000000000000), (53006201815115764320021341327/365242265799206400000000000000), (20988043749633593264040589501/152184277416336000000000000000), (22291761804267451665470075921/190230346770420000000000000000)]
    reserve := (29295748789/250000000000) }

theorem quarter_021_010_valid : quarter_021_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_021_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_021_010]
  · intro i; fin_cases i <;> norm_num [quarter_021_010]
  · norm_num [quarter_021_010]
  · norm_num [quarter_021_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_021_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_021_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_021_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_021_010]

def quarter_021_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 1]
    lambda := ![(216981/5000000), (102279/2500000), (133381/4000000), (10074713/100000000), (10074713/100000000), (10074713/100000000), (58010557/100000000)]
    cone := fun i => (![![0, 0, (6301999/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (57129019/100000000), 0, 0]] i.1) i.2
    mu := ![(6844337/50000000), (110493/50000000), (133363/10000000), (670373/25000000), (1/100000000), (1/100000000), (91009/25000000)]
    alternative := .zero
    polynomial := [(-83708925950906374034893488559671205081/136738197184190656118256651800000000000), (-587418371788661/36403600000000), (-6362776423670961320848068911688608338331/68369098592095328059128325900000000000), (-587418371788661/36403600000000), (-12641843921391016267661244334817545471581/136738197184190656118256651800000000000)]
    bernstein := [(106222727493328755095498977324144261107219/1367381971841906561182566518000000000000000), (505650894002466760526998659582137257692307/5469527887367626244730266072000000000000000), (6395824032282677219887340782698364035553513/65634334648411514936763192864000000000000000), (8117433508834314984514504182521033386928163/87512446197882019915684257152000000000000000), (27453535890721307090033419287700274633449139/350049784791528079662737028608000000000000000)]
    reserve := (77683287977/1000000000000) }

theorem quarter_021_011_valid : quarter_021_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_021_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_021_011]
  · intro i; fin_cases i <;> norm_num [quarter_021_011]
  · norm_num [quarter_021_011]
  · norm_num [quarter_021_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_021_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_021_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_021_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_021_011]

def quarter_021_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 1, 0, 2, 0, 0, 1]
    lambda := ![(11489121/100000000), (5485391/50000000), (7609291/100000000), (17663889/100000000), (17663889/100000000), (17663889/100000000), (8469569/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4173901/20000000), 0, 0]] i.1) i.2
    mu := ![(206873/4000000), (222043/50000000), (3373627/100000000), (2429917/50000000), (1/100000000), (1/100000000), (2080947/50000000)]
    alternative := .zero
    polynomial := [(17480167297426410075532529925397565089949/783592771996562443385168792247000000000000), (-65088252824983/69364900000000), (-1427344968820478275424121947778068724230051/391796385998281221692584396123500000000000), (-65088252824983/69364900000000), (-957390034979460986974592141827178337850017/261197590665520814461722930749000000000000)]
    bernstein := [(145377078994323981884565778012694504376555617069/2005997496311199855066032108152320000000000000000), (70171431790155244644027057611801174809426706623/1002998748155599927533016054076160000000000000000), (100924248628419125049722968427416699786751973823/1504498122233399891299524081114240000000000000000), (5335281102859206752134993841131674678076625949/83583229012966660627751337839680000000000000000), (7549031250246492793241588777162286460324049149/125374843519449990941627006759520000000000000000)]
    reserve := (30105845153/500000000000) }

theorem quarter_021_012_valid : quarter_021_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_021_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_021_012]
  · intro i; fin_cases i <;> norm_num [quarter_021_012]
  · norm_num [quarter_021_012]
  · norm_num [quarter_021_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_021_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_021_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_021_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_021_012]

def quarter_021_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 1]
    lambda := ![(5125193/50000000), (499883/5000000), (3827181/50000000), (9848533/50000000), (9848533/50000000), (9848533/50000000), (2601279/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (357189/2000000), 0, 0]] i.1) i.2
    mu := ![(836881/20000000), (52667/20000000), (1590793/50000000), (5339647/100000000), (1/100000000), (1/100000000), (993523/20000000)]
    alternative := .zero
    polynomial := [(1359595148066550027548969216914313876051/37196873074307431156914559639100000000000), (-35551687229887/49676150000000), (-79715061726230229509197022214558913246949/18598436537153715578457279819550000000000), (-35551687229887/49676150000000), (-160789718600527009045943013646032140369949/37196873074307431156914559639100000000000)]
    bernstein := [(367100029068141658750830614413726524957390851/5951499691889188985106329542256000000000000000), (712606254886858117686806281538287999340561251/11902999383778377970212659084512000000000000000), (4114504935596048516564081139764332874272895353/71417996302670267821275954507072000000000000000), (2614562731543909304208312797359941847692762451/47611997535113511880850636338048000000000000000), (4930101269153479000109318496356817334798273251/95223995070227023761701272676096000000000000000)]
    reserve := (51773728517/1000000000000) }

theorem quarter_021_013_valid : quarter_021_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_021_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_021_013]
  · intro i; fin_cases i <;> norm_num [quarter_021_013]
  · norm_num [quarter_021_013]
  · norm_num [quarter_021_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_021_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_021_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_021_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_021_013]

def quarter_021_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 1, 0, 2, 0, 0, 1]
    lambda := ![(1844869/20000000), (1830943/20000000), (3791171/50000000), (10642937/50000000), (10642937/50000000), (10642937/50000000), (407239/4000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3134047/20000000), 0, 0]] i.1) i.2
    mu := ![(3471393/100000000), (11739/10000000), (3003607/100000000), (1427391/25000000), (1/100000000), (1/100000000), (5554481/100000000)]
    alternative := .zero
    polynomial := [(680737092655700912970829293585160308539/15403658580338370180385305213000000000000), (-15920516605149/27772405000000), (-56935675677307975344069094760225525178961/7701829290169185090192652606500000000000), (-15920516605149/27772405000000), (-2664002056913294223281605088698516527127/358224618147403957683379191000000000000)]
    bernstein := [(2125860357632540774534351041983378304892498339/39433365965666227661786381345280000000000000000), (1297203037092584691259312712419015268954689/24645853728541392288616488340800000000000000), (3740410721371536010365302766157073279808239/73937561185624176865849465022400000000000000), (735925462687105038330140882304798779789/15403658580338370180385305213000000000000), (680737092655700912970829293585160308539/15403658580338370180385305213000000000000)]
    reserve := (5524151041/125000000000) }

theorem quarter_021_014_valid : quarter_021_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_021_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_021_014]
  · intro i; fin_cases i <;> norm_num [quarter_021_014]
  · norm_num [quarter_021_014]
  · norm_num [quarter_021_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_021_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_021_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_021_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_021_014]

def quarter_021_015 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 1]
    lambda := ![0, (5407977/50000000), (920521/10000000), (6664903/25000000), (6664903/25000000), (6664903/25000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(162197/20000000), 0, (5406287/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6962277/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (68319/100000000), (143551/4000000), (712661/10000000), (1/100000000), (1/100000000), (6962277/100000000)]
    alternative := .zero
    polynomial := [(101528663575161376186663790348843/2317195728810001596933000000000000), (4873602174017/11386500000000), (-19731322242918268232489189459511157/1158597864405000798466500000000000), (4873602174017/11386500000000), (-39564173149411697841165042709371157/2317195728810001596933000000000000)]
    bernstein := [(101528663575161376186663790348843/2317195728810001596933000000000000), (215454782625612932129119429114111/4634391457620003193866000000000000), (527114049199249200291297876613775243/11122539498288007665278400000000000000), (344949262691548020339902414444531711/7415026332192005110185600000000000000), (260248227292931901920925529786921566443/5932021065753604088148480000000000000000)]
    reserve := (2738457263/62500000000) }

theorem quarter_021_015_valid : quarter_021_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_021_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_021_015]
  · intro i; fin_cases i <;> norm_num [quarter_021_015]
  · norm_num [quarter_021_015]
  · norm_num [quarter_021_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_021_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_021_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_021_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_021_015]

def quarter_021_016 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 1, 0, 2, 0, 0, 1]
    lambda := ![0, (12374313/100000000), (9762173/100000000), (5190901/20000000), (5190901/20000000), (5190901/20000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(385937/25000000), 0, (12339559/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1355627/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (7809/10000000), (1991303/50000000), (7006741/100000000), (1/100000000), (1/100000000), (847267/12500000)]
    alternative := .zero
    polynomial := [(319735940994809581603014021174819/12956397333438995958536000000000000), (76454284518171/52060000000000), (-126351957163608386336838599984709181/6478198666719497979268000000000000), (76454284518171/52060000000000), (-253023650268211582255280213990593181/12956397333438995958536000000000000)]
    bernstein := [(1632466361240364639878033221918271371619/33168377173603829653852160000000000000000), (867530583006740350769519993814474458419/16584188586801914826926080000000000000000), (189685262873288747919114356471254834751/3553754697171838891484160000000000000000), (217300934385735589531331855872274559619/4146047146700478706731520000000000000000), (102423778662666183514255429619128054019/2073023573350239353365760000000000000000)]
    reserve := (49217552993/1000000000000) }

theorem quarter_021_016_valid : quarter_021_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_021_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_021_016]
  · intro i; fin_cases i <;> norm_num [quarter_021_016]
  · norm_num [quarter_021_016]
  · norm_num [quarter_021_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_021_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_021_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_021_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_021_016]

def quarter_021_017 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 1]
    lambda := ![0, (3523747/25000000), (10295459/100000000), (5040637/20000000), (5040637/20000000), (5040637/20000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(2454283/100000000), 0, (13985299/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1645481/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (44377/50000000), (1102611/25000000), (1719799/25000000), (1/100000000), (1/100000000), (263277/4000000)]
    alternative := .zero
    polynomial := [(-8474731950023857961849300112013/296883819584460748584000000000000), (123684791772667/44377000000000), (-3305369340733394125484474275872013/148441909792230374292000000000000), (123684791772667/44377000000000), (-6602263949516764393007099251632013/296883819584460748584000000000000)]
    bernstein := [(2629341999285267365938992838125957587/47501411133513719773440000000000000000), (5597257769944619564149065021593437961/95002822267027439546880000000000000000), (34297858398752208647260083126333983249/570016933602164637281280000000000000000), (22460894568331919723202326254774059649/380011289068109758187520000000000000000), (42340463742351720040891133209243672547/760022578136219516375040000000000000000)]
    reserve := (55352923977/1000000000000) }

theorem quarter_021_017_valid : quarter_021_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_021_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_021_017]
  · intro i; fin_cases i <;> norm_num [quarter_021_017]
  · norm_num [quarter_021_017]
  · norm_num [quarter_021_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_021_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_021_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_021_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_021_017]

def quarter_021_018 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 1, 0, 2, 0, 0, 1]
    lambda := ![0, (15986529/100000000), (2159377/20000000), (24405529/100000000), (24405529/100000000), (24405529/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1781783/50000000), 0, (3148719/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6373613/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (100321/100000000), (974889/20000000), (6743303/100000000), (1/100000000), (1/100000000), (3186807/50000000)]
    alternative := .zero
    polynomial := [(-27603307095978718718886093838720199/215561324740306399509564000000000000), (2731371033897/617360000000), (-2731605781152726671884027502190820199/107780662370153199754782000000000000), (2731371033897/617360000000), (-5435608255209474625049168910542920199/215561324740306399509564000000000000)]
    bernstein := [(34365939009418701530956431004302966292681/551836991335184382744483840000000000000000), (704311814143098364700059864738881519079/10612249833368930437393920000000000000000), (7018862800938676930615133599378871431927/103469435875347071764590720000000000000000), (44216744016001424148840611896310731931/663265614585558152337120000000000000000), (135449988981662604061282237903406550001/2155613247403063995095640000000000000000)]
    reserve := (12455105239/200000000000) }

theorem quarter_021_018_valid : quarter_021_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_021_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_021_018]
  · intro i; fin_cases i <;> norm_num [quarter_021_018]
  · norm_num [quarter_021_018]
  · norm_num [quarter_021_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_021_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_021_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_021_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_021_018]

def quarter_021_019 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 1, 0, 2, 0, 0, 1]
    lambda := ![0, (18056407/100000000), (11257853/100000000), (23561913/100000000), (23561913/100000000), (23561913/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(4892169/100000000), 0, (8802533/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6153299/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (22557/20000000), (5376643/100000000), (3299151/50000000), (1/100000000), (1/100000000), (6153299/100000000)]
    alternative := .zero
    polynomial := [(-236536056382198918652676164022799841/820694452815445589461833000000000000), (724407827288899/112785000000000), (-11802162243764740930815320911891677841/410347226407722794730916500000000000), (724407827288899/112785000000000), (-7789262810382427647659321886586851947/273564817605148529820611000000000000)]
    bernstein := [(574797706653707568554251741281215327959/8206944528154455894618330000000000000000), (490590534191619303941106668557846453679/6565555622523564715694664000000000000000), (1204372931386170237472682732546168189633/15757333494056555317667193600000000000000), (63155885576243996301863908085015882287/840391119683016283608916992000000000000), (3175356026175918874715264145783826077/44820859716427535125808906240000000000)]
    reserve := (17509491647/250000000000) }

theorem quarter_021_019_valid : quarter_021_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_021_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_021_019]
  · intro i; fin_cases i <;> norm_num [quarter_021_019]
  · norm_num [quarter_021_019]
  · norm_num [quarter_021_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_021_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_021_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_021_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_021_019]

def quarter_021_020 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 1, 0, 2, 0, 0, 1]
    lambda := ![0, (2538807/12500000), (291737/2500000), (4534671/20000000), (4534671/20000000), (4534671/20000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1614893/25000000), 0, (19556717/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (185039/3125000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (31531/25000000), (2959409/50000000), (6443379/100000000), (1/100000000), (1/100000000), (5921249/100000000)]
    alternative := .zero
    polynomial := [(-29943408693317641842529350884848445347/56962588868118273292502544000000000000), (278341402195461/31531000000000), (-926912778817515180680977995173079005347/28481294434059136646251272000000000000), (278341402195461/31531000000000), (-1823882148941712719519426639461309565347/56962588868118273292502544000000000000)]
    bernstein := [(734394426611020924646836683633399795557/9332750560152497896243616808960000000000), (9803355831086920851560000996427086431307/116659382001906223703045210112000000000000), (376314303672378140931047790693837714513119/4374726825071483388864195379200000000000000), (308491697633488995670999003643696367507551/3645605687559569490720162816000000000000000), (727240827773191982413996551121748433748493/9114014218898923726800407040000000000000000)]
    reserve := (78690030541/1000000000000) }

theorem quarter_021_020_valid : quarter_021_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_021_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_021_020]
  · intro i; fin_cases i <;> norm_num [quarter_021_020]
  · norm_num [quarter_021_020]
  · norm_num [quarter_021_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_021_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_021_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_021_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_021_020]

def quarter_021_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 1]
    lambda := ![0, (22752159/100000000), (46964/390625), (10870843/50000000), (10870843/50000000), (10870843/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(8283289/100000000), 0, (10790737/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5677939/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (28059/20000000), (6502317/100000000), (784713/12500000), (1/100000000), (1/100000000), (5677939/100000000)]
    alternative := .zero
    polynomial := [(-25872886027269561354714553299571369/30107738347417273621423000000000000), (546371506586109/46765000000000), (-552750396732980253950976502206873369/15053869173708636810711500000000000), (546371506586109/46765000000000), (-1079627907438690946547238451114175369/30107738347417273621423000000000000)]
    bernstein := [(425251759510302174720546765873372150311/4817238135586763779427680000000000000000), (19341672076058333033299715796076387997/204988856833479309762880000000000000000), (1862363378658669974956633376307139228671/19268952542347055117710720000000000000000), (3666011208492819840987525607682589037099/38537905084694110235421440000000000000000), (6916135602453938724548480894963189775831/77075810169388220470842880000000000000000)]
    reserve := (3531083559/40000000000) }

theorem quarter_021_021_valid : quarter_021_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_021_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_021_021]
  · intro i; fin_cases i <;> norm_num [quarter_021_021]
  · norm_num [quarter_021_021]
  · norm_num [quarter_021_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_021_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_021_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_021_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_021_021]

def quarter_021_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 1, 0, 2, 0, 0, 1]
    lambda := ![0, (5076353/20000000), (6154481/50000000), (10384879/50000000), (10384879/50000000), (10384879/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1037779/10000000), 0, (23657721/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1084823/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (4851/3125000), (1781959/25000000), (12201/200000), (1/100000000), (1/100000000), (1356029/25000000)]
    alternative := .zero
    polynomial := [(-163182482039200230051082784811593/124533450514070446464000000000000), (933531565025887/62092800000000), (-2571809188764138799625060241711593/62266725257035223232000000000000), (933531565025887/62092800000000), (-4980435895489077369199037698611593/124533450514070446464000000000000)]
    bernstein := [(10503401434515901156296607536743634269/106268544438673447649280000000000000000), (66878191236383855571231076278517827/632550859754008616960000000000000000), (404876490689581775612892725765472451/3736003515422113393920000000000000000), (3691690608521937588639922127858693/34592625142797346240000000000000000), (1959531747594818019968496207215783/19458351642823507260000000000000000)]
    reserve := (98838292083/1000000000000) }

theorem quarter_021_022_valid : quarter_021_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_021_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_021_022]
  · intro i; fin_cases i <;> norm_num [quarter_021_022]
  · norm_num [quarter_021_022]
  · norm_num [quarter_021_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_021_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_021_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_021_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_021_022]

def quarter_021_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 1]
    lambda := ![0, (7048811/25000000), (12519761/100000000), (3952333/20000000), (3952333/20000000), (3952333/20000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(2550639/20000000), 0, (12879439/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5160847/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (170837/100000000), (487197/6250000), (2955567/50000000), (1/100000000), (1/100000000), (322553/6250000)]
    alternative := .zero
    polynomial := [(-201196215727471493273380357114499663/105795494473468910254452000000000000), (808163880714421/42709250000000), (-2450033537434172402859374800093859663/52897747236734455127226000000000000), (808163880714421/42709250000000), (-4698870859140873312445369243073219663/105795494473468910254452000000000000)]
    bernstein := [(1825046639946318648505359930180956953/16530546011479517227258125000000000000), (2841756899663625012222682074624143239/24044430562152025057830000000000000000), (54961655162158865465686190854744487497/453409262029152472519080000000000000000), (8965251991263795661959635843809222523/75065539315986809936640000000000000000), (744777572884058246455196525936292246377/6605767459806839274424320000000000000000)]
    reserve := (22080899671/200000000000) }

theorem quarter_021_023_valid : quarter_021_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_021_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_021_023]
  · intro i; fin_cases i <;> norm_num [quarter_021_023]
  · norm_num [quarter_021_023]
  · norm_num [quarter_021_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_021_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_021_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_021_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_021_023]

def quarter_021_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 1, 0, 2, 0, 0, 1]
    lambda := ![0, (15591553/50000000), (6323983/50000000), (585093/3125000), (585093/3125000), (585093/3125000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(15413753/100000000), 0, (3481637/12500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4889589/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (186979/100000000), (2125703/25000000), (5709231/100000000), (1/100000000), (1/100000000), (4889589/100000000)]
    alternative := .zero
    polynomial := [(-4915354187788985281869230074454124137/1849243660872480171200830500000000000), (1093053478517523/46744750000000), (-3681957846398961565988186294334929549/71124756187403083507724250000000000), (1093053478517523/46744750000000), (-90815549818584015433823613578254044137/1849243660872480171200830500000000000)]
    bernstein := [(582271363504047466266347752471404837626743/4734063771833549238274126080000000000000000), (62374875524275078694049935073413761489807/473406377183354923827412608000000000000000), (1477212349508947183256562695060402368249/10924762550385113626786444800000000000000), (631016229137731101089709237058821788399/4734063771833549238274126080000000000000), (59594564974479882537198976792980836407/473406377183354923827412608000000000000)]
    reserve := (24599219257/200000000000) }

theorem quarter_021_024_valid : quarter_021_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_021_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_021_024]
  · intro i; fin_cases i <;> norm_num [quarter_021_024]
  · norm_num [quarter_021_024]
  · norm_num [quarter_021_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_021_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_021_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_021_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_021_024]

def quarter_021_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 1]
    lambda := ![0, (2145573/6250000), (12687997/100000000), (3532189/20000000), (3532189/20000000), (3532189/20000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1147259/6250000), 0, (747579/2500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (922447/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (203489/100000000), (4623901/50000000), (5494813/100000000), (1/100000000), (1/100000000), (922447/20000000)]
    alternative := .zero
    polynomial := [(-25785144665641513816090628983590574537/7153771489222046126842618500000000000), (18088238157489/635903125000), (-206229995213786382146240587330168174537/3576885744611023063421309250000000000), (18088238157489/635903125000), (-386674845761931250476390545676745774537/7153771489222046126842618500000000000)]
    bernstein := [(250202245775264553952902255026224118807/1831365501240843808471710336000000000000), (81271322774348552455884526284703184877/554959242800255699536881920000000000000), (82617773309287561302484740320508689818157/549409650372253142541513100800000000000000), (6964376853621062256305862481288089714147/46958089775406251499274624000000000000000), (2566278703406946312737455935480584460357383/18313655012408438084717103360000000000000000)]
    reserve := (8538787233/62500000000) }

theorem quarter_021_025_valid : quarter_021_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_021_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_021_025]
  · intro i; fin_cases i <;> norm_num [quarter_021_025]
  · norm_num [quarter_021_025]
  · norm_num [quarter_021_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_021_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_021_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_021_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_021_025]

def quarter_021_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 1, 0, 2, 0, 0, 1]
    lambda := ![0, (18804687/50000000), (12636607/100000000), (16584673/100000000), (16584673/100000000), (16584673/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(539193/2500000), 0, (31866739/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4331161/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (220157/100000000), (10025217/100000000), (1053691/20000000), (1/100000000), (1/100000000), (2165581/50000000)]
    alternative := .zero
    polynomial := [(-96006474147084764519340222304861277519/20145310930854737130729996000000000000), (7512240425467107/220157000000000), (-644340515908516756927289768215599317519/10072655465427368565364998000000000000), (7512240425467107/220157000000000), (-1192674557669948749335239314126337357519/20145310930854737130729996000000000000)]
    bernstein := [(7801316911545547748068607493498256831607521/51571995982988127054668789760000000000000000), (2091795085395218510759169456677210009973833/12892998995747031763667197440000000000000000), (1611808194748241071323752035674545338068727/9669749246810273822750398080000000000000000), (132538462581742034496067422917615069625757/805812437234189485229199840000000000000000), (31321078004697363374851420700574156236761/201453109308547371307299960000000000000000)]
    reserve := (151270408733/1000000000000) }

theorem quarter_021_026_valid : quarter_021_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_021_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_021_026]
  · intro i; fin_cases i <;> norm_num [quarter_021_026]
  · norm_num [quarter_021_026]
  · norm_num [quarter_021_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_021_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_021_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_021_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_021_026]

def quarter_021_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 1]
    lambda := ![0, (20495427/50000000), (1561703/12500000), (7752587/50000000), (7752587/50000000), (7752587/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(25024843/100000000), 0, (8424277/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2024623/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (236729/100000000), (10827981/100000000), (5031449/100000000), (1/100000000), (1/100000000), (2024623/50000000)]
    alternative := .zero
    polynomial := [(-80489331281251106827131520541818785077/13055881332353702135909161500000000000), (1195907530091763/29591125000000), (-461383506349101397216088653554802245077/6527940666176851067954580750000000000), (1195907530091763/29591125000000), (-842277681416951687605045786567785705077/13055881332353702135909161500000000000)]
    bernstein := [(21792983634787188684305715106064093460163/130558813323537021359091615000000000000000), (93542862077863728728279316435187781150473/522235253294148085436366460000000000000000), (1153829679201608531179587688939081565558749/6266823039529777025236397520000000000000000), (1518804570641983918373388836361181488157493/8355764052706369366981863360000000000000000), (5745449999566446995797052230197389975654203/33423056210825477467927453440000000000000000)]
    reserve := (166920815837/1000000000000) }

theorem quarter_021_027_valid : quarter_021_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_021_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_021_027]
  · intro i; fin_cases i <;> norm_num [quarter_021_027]
  · norm_num [quarter_021_027]
  · norm_num [quarter_021_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_021_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_021_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_021_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_021_027]

def quarter_021_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 1, 0, 2, 0, 0, 1]
    lambda := ![0, (44431431/100000000), (12262653/100000000), (7217653/50000000), (7217653/50000000), (7217653/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(5738317/20000000), 0, (17672229/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (753969/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (126457/50000000), (1164667/10000000), (239297/5000000), (1/100000000), (1/100000000), (753969/20000000)]
    alternative := .zero
    polynomial := [(-138565315647193650608806565762228021/17715121271399935234978000000000000), (11962879368651651/252914000000000), (-688552906435138945995660623751458021/8857560635699967617489000000000000), (11962879368651651/252914000000000), (-1238540497223084241382514681740688021/17715121271399935234978000000000000)]
    bernstein := [(8323130396103100359081521313661214675419/45350710454783834201543680000000000000000), (4467655404044495405240351640735632573241/22675355227391917100771840000000000000000), (6891608309763113604548031044147626563097/34013032841087875651157760000000000000000), (1134488683728111141363180081503949601761/5668838806847979275192960000000000000000), (536727856059392967864838972030467498379/2834419403423989637596480000000000000000)]
    reserve := (11470507177/62500000000) }

theorem quarter_021_028_valid : quarter_021_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_021_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_021_028]
  · intro i; fin_cases i <;> norm_num [quarter_021_028]
  · norm_num [quarter_021_028]
  · norm_num [quarter_021_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_021_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_021_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_021_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_021_028]

def quarter_021_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 1, 0, 2, 0, 0, 1]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(13583621/20000000), 0, (19192791/25000000), 0, 0], ![0, 0, (26115447/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (560543/100000000), (3264431/12500000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-225687117940091736631685173/10979123676198000000000000), (320397734/2802715), (-977529620943143736631685173/5489561838099000000000000), (320397734/2802715), (-1729372123946195736631685173/10979123676198000000000000)]
    bernstein := [(314235498496942627315637438027/1756659788191680000000000000000), (146182140136763496479577675463/702663915276672000000000000000), (184737751281415488041979179273/843196698332006400000000000000), (23792104293952627085543809151/112426226444267520000000000000), (8326718578362657089749713083/44970490577707008000000000000)]
    reserve := (44720597097/250000000000) }

theorem quarter_021_029_valid : quarter_021_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_021_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_021_029]
  · intro i; fin_cases i <;> norm_num [quarter_021_029]
  · norm_num [quarter_021_029]
  · norm_num [quarter_021_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_021_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_021_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_021_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_021_029]

def quarterTable021 : OwnerTable where
  mode := .quarter
  owners := ![0, 1, 0, 2, 0, 0, 1]
  rows := [quarter_021_000, quarter_021_001, quarter_021_002, quarter_021_003, quarter_021_004, quarter_021_005, quarter_021_006, quarter_021_007, quarter_021_008, quarter_021_009, quarter_021_010, quarter_021_011, quarter_021_012, quarter_021_013, quarter_021_014, quarter_021_015, quarter_021_016, quarter_021_017, quarter_021_018, quarter_021_019, quarter_021_020, quarter_021_021, quarter_021_022, quarter_021_023, quarter_021_024, quarter_021_025, quarter_021_026, quarter_021_027, quarter_021_028, quarter_021_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_021_000_valid
    · exact quarter_021_001_valid
    · exact quarter_021_002_valid
    · exact quarter_021_003_valid
    · exact quarter_021_004_valid
    · exact quarter_021_005_valid
    · exact quarter_021_006_valid
    · exact quarter_021_007_valid
    · exact quarter_021_008_valid
    · exact quarter_021_009_valid
    · exact quarter_021_010_valid
    · exact quarter_021_011_valid
    · exact quarter_021_012_valid
    · exact quarter_021_013_valid
    · exact quarter_021_014_valid
    · exact quarter_021_015_valid
    · exact quarter_021_016_valid
    · exact quarter_021_017_valid
    · exact quarter_021_018_valid
    · exact quarter_021_019_valid
    · exact quarter_021_020_valid
    · exact quarter_021_021_valid
    · exact quarter_021_022_valid
    · exact quarter_021_023_valid
    · exact quarter_021_024_valid
    · exact quarter_021_025_valid
    · exact quarter_021_026_valid
    · exact quarter_021_027_valid
    · exact quarter_021_028_valid
    · exact quarter_021_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
