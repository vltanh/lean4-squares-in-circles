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

def quarter_045_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 3, 0, 2, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (305109/781250), (476141/781250)]
    cone := fun i => (![![0, 0, (14961777/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(305109/1562500), 0, (305109/781250), 0, 0], ![0, 0, (46788991/100000000), 0, 0]] i.1) i.2
    mu := ![(13862837/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (341629/100000000)]
    alternative := .zero
    polynomial := [(-14374691271790946411340937/1183986785368250000000000), (-9297593879616/133448828125), (-63788844655569788786860937/591993392684125000000000), (-9297593879616/133448828125), (-113202998039348631162380937/1183986785368250000000000)]
    bernstein := [(2990005041502588170728626727/4849609872868352000000000000), (7620368667567275881374279419/12124024682170880000000000000), (57200606057925900106726513837/90930185116281600000000000000), (46860259961119773118474510947/75775154263568000000000000000), (113063918489006412728021519863/189437885658920000000000000000)]
    reserve := (14920975033/25000000000) }

theorem quarter_045_000_valid : quarter_045_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_045_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_045_000]
  · intro i; fin_cases i <;> norm_num [quarter_045_000]
  · norm_num [quarter_045_000]
  · norm_num [quarter_045_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_045_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_045_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_045_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_045_000]

def quarter_045_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (37732553/100000000), (62267447/100000000)]
    cone := fun i => (![![0, 0, (1528617/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(18866277/100000000), 0, (37732553/100000000), 0, 0], ![0, 0, (4953271/10000000), 0, 0]] i.1) i.2
    mu := ![(14163403/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (354441/100000000)]
    alternative := .zero
    polynomial := [(-107611658598710606406360499/10040181445446000000000000), (-2349509744102191/35444100000000), (-181483337459563315242486833/1673363574241000000000000), (-2349509744102191/35444100000000), (-981288366158669285048560499/10040181445446000000000000)]
    bernstein := [(919532253676100215105530441101/1606429031271360000000000000000), (1879851632914358466935883430559/3212858062542720000000000000000), (3767188926728837572299399960181/6425716125085440000000000000000), (7404713308036821615973784746679/12851432250170880000000000000000), (14266927128878180023579413088861/25702864500341760000000000000000)]
    reserve := (277535741759/500000000000) }

theorem quarter_045_001_valid : quarter_045_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_045_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_045_001]
  · intro i; fin_cases i <;> norm_num [quarter_045_001]
  · norm_num [quarter_045_001]
  · norm_num [quarter_045_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_045_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_045_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_045_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_045_001]

def quarter_045_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 3, 0, 2, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (36281179/100000000), (63718821/100000000)]
    cone := fun i => (![![0, 0, (15642471/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1814059/10000000), 0, (36281179/100000000), 0, 0], ![0, 0, (6547619/12500000), 0, 0]] i.1) i.2
    mu := ![(7246767/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (367987/100000000)]
    alternative := .zero
    polynomial := [(-8328927597030419362173933/888905349343000000000000), (-2311793950369959/36798700000000), (-48640910973048999170613933/444452674671500000000000), (-2311793950369959/36798700000000), (-88952894349067578979053933/888905349343000000000000)]
    bernstein := [(1201621007407386091306135973187/2275597694318080000000000000000), (308040043995528656192395392597/568899423579520000000000000000), (77265236295115823350674097207/142224855894880000000000000000), (18976090232022837413552977017/35556213973720000000000000000), (4559949838646291704679922027/8889053493430000000000000000)]
    reserve := (128246214347/250000000000) }

theorem quarter_045_002_valid : quarter_045_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_045_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_045_002]
  · intro i; fin_cases i <;> norm_num [quarter_045_002]
  · norm_num [quarter_045_002]
  · norm_num [quarter_045_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_045_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_045_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_045_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_045_002]

def quarter_045_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (34687529/100000000), (65312471/100000000)]
    cone := fun i => (![![0, 0, (32067399/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(3468753/20000000), 0, (34687529/100000000), 0, 0], ![0, 0, (27669903/50000000), 0, 0]] i.1) i.2
    mu := ![(14856027/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (95581/25000000)]
    alternative := .zero
    polynomial := [(-22993938576098725413408389/2839907833374000000000000), (-2265528231874159/38232400000000), (-157232236230409305195663389/1419953916687000000000000), (-2265528231874159/38232400000000), (-291470533884719884977918389/2839907833374000000000000)]
    bernstein := [(13721315095064621478401170291/28399078333740000000000000000), (56494547290367897220467356867/113596313334960000000000000000), (681225850798745907422906180437/1363155760019520000000000000000), (891783001585839687797971583423/1817541013359360000000000000000), (3418956771277319837318513405851/7270164053437440000000000000000)]
    reserve := (470272300067/1000000000000) }

theorem quarter_045_003_valid : quarter_045_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_045_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_045_003]
  · intro i; fin_cases i <;> norm_num [quarter_045_003]
  · norm_num [quarter_045_003]
  · norm_num [quarter_045_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_045_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_045_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_045_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_045_003]

def quarter_045_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 3, 0, 2, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (32937947/100000000), (67062053/100000000)]
    cone := fun i => (![![0, 0, (2057901/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(8234487/50000000), 0, (32937947/100000000), 0, 0], ![0, 0, (29207921/50000000), 0, 0]] i.1) i.2
    mu := ![(3813497/25000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (79503/20000000)]
    alternative := .zero
    polynomial := [(-522976290930603728141567/75796112997750000000000), (-2208886347425191/39751500000000), (-1419268948894550494390689/12632685499625000000000), (-2208886347425191/39751500000000), (-7992637402436699238202567/75796112997750000000000)]
    bernstein := [(84874092072739102667061094153/194038049274240000000000000000), (8777224093450606029420858503/19403804927424000000000000000), (294530147709546860396101443/646793497580800000000000000), (86680303311943665214532231/194038049274240000000000000), (8277382639847301395568137/19403804927424000000000000)]
    reserve := (426585541897/1000000000000) }

theorem quarter_045_004_valid : quarter_045_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_045_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_045_004]
  · intro i; fin_cases i <;> norm_num [quarter_045_004]
  · norm_num [quarter_045_004]
  · norm_num [quarter_045_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_045_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_045_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_045_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_045_004]

def quarter_045_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (31017243/100000000), (68982757/100000000)]
    cone := fun i => (![![0, 0, (8467363/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7754311/50000000), 0, (31017243/100000000), 0, 0], ![0, 0, (30808081/50000000), 0, 0]] i.1) i.2
    mu := ![(15690873/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (41363/10000000)]
    alternative := .zero
    polynomial := [(-3751957175530520117015977/649021579899000000000000), (-2139654936678951/41363000000000), (-5299802024152296461536711/46358684278500000000000), (-2139654936678951/41363000000000), (-70445271162601630344497977/649021579899000000000000)]
    bernstein := [(64865702008638222482352647/166149524454144000000000000), (674792094324244282489899079/1661495244541440000000000000), (20424339739921842881447883077/49844857336243200000000000000), (9529763332552959388327432721/23735646350592000000000000000), (633906697069892355947829894503/1661495244541440000000000000000)]
    reserve := (381527843159/1000000000000) }

theorem quarter_045_005_valid : quarter_045_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_045_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_045_005]
  · intro i; fin_cases i <;> norm_num [quarter_045_005]
  · norm_num [quarter_045_005]
  · norm_num [quarter_045_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_045_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_045_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_045_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_045_005]

def quarter_045_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 3, 0, 2, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (7227123/25000000), (71091509/100000000)]
    cone := fun i => (![![0, 0, (2181551/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7227123/50000000), 0, (7227123/25000000), 0, 0], ![0, 0, (32474227/50000000), 0, 0]] i.1) i.2
    mu := ![(16170531/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (430747/100000000)]
    alternative := .zero
    polynomial := [(-33037324067310910181975111/6965407716657000000000000), (-513787079798607/10768675000000), (-406356962183206827945305111/3482703858328500000000000), (-513787079798607/10768675000000), (-779676600299102745708635111/6965407716657000000000000)]
    bernstein := [(6093119769647584902599704905529/17831443754641920000000000000000), (798528990934761674562500137481/2228930469330240000000000000000), (75741629048545712115187705363/208962231499710000000000000000), (474907964925119125600886801/1339501483972500000000000000), (28016139137347074902693557/83718842748281250000000000)]
    reserve := (2614418449/7812500000) }

theorem quarter_045_006_valid : quarter_045_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_045_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_045_006]
  · intro i; fin_cases i <;> norm_num [quarter_045_006]
  · norm_num [quarter_045_006]
  · norm_num [quarter_045_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_045_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_045_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_045_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_045_006]

def quarter_045_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (13296399/50000000), (36703601/50000000)]
    cone := fun i => (![![0, 0, (7208357/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(13296399/100000000), 0, (13296399/50000000), 0, 0], ![0, 0, (68421053/100000000), 0, 0]] i.1) i.2
    mu := ![(16697261/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (448949/100000000)]
    alternative := .zero
    polynomial := [(-11364612184292589064356729/2998487451475600000000000), (-488025723632799/11223725000000), (-179091873550159228802888729/1499243725737800000000000), (-488025723632799/11223725000000), (-346819134916025868541420729/2998487451475600000000000)]
    bernstein := [(136246441847856924563076799/468513664293062500000000000), (2310367049381714429525128261/7496218628689000000000000000), (28154514575963423602974382753/89954623544268000000000000000), (292980077649934007469982920953/959515984472192000000000000000), (2190905933801913779741503162471/7676127875777536000000000000000)]
    reserve := (57083622609/200000000000) }

theorem quarter_045_007_valid : quarter_045_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_045_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_045_007]
  · intro i; fin_cases i <;> norm_num [quarter_045_007]
  · norm_num [quarter_045_007]
  · norm_num [quarter_045_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_045_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_045_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_045_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_045_007]

def quarter_045_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 3, 0, 2, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (24049023/100000000), (75950977/100000000)]
    cone := fun i => (![![0, 0, (18645369/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(187883/1562500), 0, (24049023/100000000), 0, 0], ![0, 0, (72043011/100000000), 0, 0]] i.1) i.2
    mu := ![(1727587/10000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (468331/100000000)]
    alternative := .zero
    polynomial := [(-592130163232521009777523/202270636824250000000000), (-1826546792745471/46833100000000), (-12408257453348347240388773/101135318412125000000000), (-1826546792745471/46833100000000), (-24224384743464173471000023/202270636824250000000000)]
    bernstein := [(122784263339620107957711558377/517812830270080000000000000000), (66124220278493264215192924433/258906415135040000000000000000), (101259237814788241533305556971/388359622702560000000000000000), (104431986989384370034921429/412271361680000000000000000), (7548604663746480273710102537/32363301891880000000000000000)]
    reserve := (5831145327/25000000000) }

theorem quarter_045_008_valid : quarter_045_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_045_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_045_008]
  · intro i; fin_cases i <;> norm_num [quarter_045_008]
  · norm_num [quarter_045_008]
  · norm_num [quarter_045_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_045_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_045_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_045_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_045_008]

def quarter_045_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 3, 0, 2, 0, 0, 1]
    lambda := ![0, 0, 0, 0, 0, (664171/3125000), (2460829/3125000)]
    cone := fun i => (![![0, 0, (3866331/10000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(664171/6250000), 0, (664171/3125000), 0, 0], ![0, 0, (4739011/6250000), 0, 0]] i.1) i.2
    mu := ![(4477937/25000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (489/100000)]
    alternative := .zero
    polynomial := [(-4733832133543288874689/2189711193000000000000), (-1634411257759/47753906250), (-46140063934181650534123/364951865500000000000), (-1634411257759/47753906250), (-272106551471546614330049/2189711193000000000000)]
    bernstein := [(63056820484380790782766031/350353790880000000000000000), (9303894629255031036217799/46713838784000000000000000), (3831329916890693390789357/18685535513600000000000000), (295623248417801293123283/1494842841088000000000000), (63657156070695807467159/358762281861120000000000)]
    reserve := (44358868873/250000000000) }

theorem quarter_045_009_valid : quarter_045_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_045_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_045_009]
  · intro i; fin_cases i <;> norm_num [quarter_045_009]
  · norm_num [quarter_045_009]
  · norm_num [quarter_045_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_045_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_045_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_045_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_045_009]

def quarter_045_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 3, 0, 2, 0, 0, 1]
    lambda := ![(19301/1250000), (3812171/100000000), (4324421/100000000), (6020731/50000000), (6020731/50000000), (6020731/50000000), (27097471/50000000)]
    cone := fun i => (![![0, 0, (12721923/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (52840277/100000000), 0, 0]] i.1) i.2
    mu := ![(6251417/50000000), (41571/4000000), (35691/12500000), (3232897/100000000), (1/100000000), (1/100000000), (67703/20000000)]
    alternative := .zero
    polynomial := [(-20598255096231238372163747005354997389/21829535280595207089107019000000000000), (-327583644408667/16925750000000), (-237559364715423271572802353805075588441/2728691910074400886138377375000000000), (-327583644408667/16925750000000), (-1879876662627154934210255083435249710139/21829535280595207089107019000000000000)]
    bernstein := [(472610471288831312553986910611537639309/3576551060372718729479293992960000000000), (1085956955067758201966788272876063234811/7451148042443164019748529152000000000000), (62949560341927323720387710046373271047007/419127077387427976110854764800000000000000), (8474485127227893249414371062748531519447/58212094081587218904285384000000000000000), (28807284283185081042400036315425509287061/218295352805952070891070190000000000000000)]
    reserve := (13196471621/100000000000) }

theorem quarter_045_010_valid : quarter_045_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_045_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_045_010]
  · intro i; fin_cases i <;> norm_num [quarter_045_010]
  · norm_num [quarter_045_010]
  · norm_num [quarter_045_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_045_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_045_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_045_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_045_010]

def quarter_045_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 1]
    lambda := ![(1786729/100000000), (1033991/25000000), (4530243/100000000), (127807/1250000), (127807/1250000), (127807/1250000), (7359173/12500000)]
    cone := fun i => (![![0, 0, (27557807/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (11595747/20000000), 0, 0]] i.1) i.2
    mu := ![(424831/3125000), (142303/12500000), (119691/50000000), (141289/5000000), (1/100000000), (1/100000000), (7389/2000000)]
    alternative := .zero
    polynomial := [(-42914655453412194700102856907119777/69764182319173590730310400000000000), (-7562631386383/461812500000), (-3293026653474476913554961525955478177/34882091159586795365155200000000000), (-7562631386383/461812500000), (-6543138651495541632409820195003836577/69764182319173590730310400000000000)]
    bernstein := [(4583558859432558544453189836198412771/53664755630133531331008000000000000000), (280008258816978302944275847441752062369/2790567292766943629212416000000000000000), (3528262252847150246419950636381124312321/33486807513203323550548992000000000000000), (4489860556068439724347217904107907565621/44649076684271098067398656000000000000000), (15354864040289622880279057451555749483663/178596306737084392269594624000000000000000)]
    reserve := (85410970489/1000000000000) }

theorem quarter_045_011_valid : quarter_045_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_045_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_045_011]
  · intro i; fin_cases i <;> norm_num [quarter_045_011]
  · norm_num [quarter_045_011]
  · norm_num [quarter_045_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_045_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_045_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_045_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_045_011]

def quarter_045_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 3, 0, 2, 0, 0, 1]
    lambda := ![(4405009/100000000), (2118831/20000000), (11290369/100000000), (224719/1000000), (224719/1000000), (224719/1000000), (393423/6250000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1190973/10000000), 0, 0]] i.1) i.2
    mu := ![(242667/12500000), (1449557/50000000), (11231/2500000), (3177291/50000000), (1/100000000), (1/100000000), (5700953/100000000)]
    alternative := .zero
    polynomial := [(3107579055137479889983222016293927065649/47706509273525661509273278098000000000000), (-26224895647863/57009530000000), (-63539414679577572814839657030212507485601/23853254636762830754636639049000000000000), (-26224895647863/57009530000000), (-130186408414292625519662536076718942036851/47706509273525661509273278098000000000000)]
    bernstein := [(10352144332686985333929240481351547432835146269/122128663740225693463739591930880000000000000000), (468345296848235321602750796231774538051592093/5551302897282986066533617815040000000000000000), (7665979566364381805877342820748624656934190223/91596497805169270097804693948160000000000000000), (114834592172276581427069675282608274861760677/1387825724320746516633404453760000000000000000), (622253219829725680612318316124853168289322349/7633041483764105841483724495680000000000000000)]
    reserve := (81521005899/1000000000000) }

theorem quarter_045_012_valid : quarter_045_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_045_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_045_012]
  · intro i; fin_cases i <;> norm_num [quarter_045_012]
  · norm_num [quarter_045_012]
  · norm_num [quarter_045_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_045_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_045_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_045_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_045_012]

def quarter_045_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 1]
    lambda := ![(3770541/100000000), (2761067/25000000), (2876151/25000000), (23029257/100000000), (23029257/100000000), (23029257/100000000), (2296409/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (262607/2500000), 0, 0]] i.1) i.2
    mu := ![(1501501/100000000), (2948819/100000000), (30733/10000000), (813093/12500000), (1/100000000), (1/100000000), (59519/1000000)]
    alternative := .zero
    polynomial := [(320663656585108887849004745133994416319/4390189703902555670215055206000000000000), (-118618971747313/297595000000000), (-8932479385486400346029078216524141783681/2195094851951277835107527603000000000000), (-118618971747313/297595000000000), (-18185622427557909579907161178182277983681/4390189703902555670215055206000000000000)]
    bernstein := [(58176168053681789055111137020471538656359519/702430352624408907234408832960000000000000000), (116417476508458850017424261581017536701089119/1404860705248817814468817665920000000000000000), (695320649664267252213719634029475465985903757/8429164231492906886812905995520000000000000000), (459050361807506882146631550399513034254835919/5619442820995271257875270663680000000000000000), (904360070935264057229513602064138919806573119/11238885641990542515750541327360000000000000000)]
    reserve := (80467058723/1000000000000) }

theorem quarter_045_013_valid : quarter_045_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_045_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_045_013]
  · intro i; fin_cases i <;> norm_num [quarter_045_013]
  · norm_num [quarter_045_013]
  · norm_num [quarter_045_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_045_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_045_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_045_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_045_013]

def quarter_045_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 3, 0, 2, 0, 0, 1]
    lambda := ![0, (1560613/12500000), (791447/6250000), (3118831/12500000), (3118831/12500000), (3118831/12500000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (369813/10000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6515973/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (16227/500000), (165071/100000000), (7070031/100000000), (1/100000000), (1/100000000), (3257987/50000000)]
    alternative := .zero
    polynomial := [(1490788060251665571537977664582871/18281250782668746852696000000000000), (-1560613/6250000), (-86054374928531617904723258902457129/9140625391334373426348000000000000), (-1560613/6250000), (-173599537917314901380984495469497129/18281250782668746852696000000000000)]
    bernstein := [(3833199192771439141643283355225284650071/46800002003631991942901760000000000000000), (2436178848044687490530800051603184471/29250001252269994964313600000000000000), (7343615907505316127385023572516123671/87750003756809984892940800000000000000), (1519318017879358592570004127230871/18281250782668746852696000000000000), (1490788060251665571537977664582871/18281250782668746852696000000000000)]
    reserve := (40773688791/500000000000) }

theorem quarter_045_014_valid : quarter_045_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_045_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_045_014]
  · intro i; fin_cases i <;> norm_num [quarter_045_014]
  · norm_num [quarter_045_014]
  · norm_num [quarter_045_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_045_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_045_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_045_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_045_014]

def quarter_045_015 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 1]
    lambda := ![0, (16351/125000), (13076713/100000000), (12307081/50000000), (12307081/50000000), (12307081/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (3874639/100000000), 0, 0], ![(326969/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6428099/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3400301/100000000), (661/800000), (3521369/50000000), (1/100000000), (1/100000000), (6428099/100000000)]
    alternative := .zero
    polynomial := [(17028328312580081620708534215065031/203503980051717978861164000000000000), (5346270119/10328125000), (-2089485609433577479096472515455718969/101751990025858989430582000000000000), (5346270119/10328125000), (-4195999547179735039813653565126502969/203503980051717978861164000000000000)]
    bernstein := [(17028328312580081620708534215065031/203503980051717978861164000000000000), (17686716964712046464884337387687431/203503980051717978861164000000000000), (85967021351417676804392202174031469831/976819104248246298533587200000000000000), (28316763609580116330925213260408473031/325606368082748766177862400000000000000), (43648084015675345860228271515501211516231/520970188932398025884579840000000000000000)]
    reserve := (83675652477/1000000000000) }

theorem quarter_045_015_valid : quarter_045_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_045_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_045_015]
  · intro i; fin_cases i <;> norm_num [quarter_045_015]
  · norm_num [quarter_045_015]
  · norm_num [quarter_045_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_045_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_045_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_045_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_045_015]

def quarter_045_016 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 3, 0, 2, 0, 0, 1]
    lambda := ![0, (6803389/50000000), (6784281/50000000), (24274887/100000000), (24274887/100000000), (24274887/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2015219/50000000), 0, 0], ![(40763/4000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1267899/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3537027/100000000), (85867/100000000), (351347/5000000), (1/100000000), (1/100000000), (792437/12500000)]
    alternative := .zero
    polynomial := [(10695630995352572181278204717053879/169120266910235645004702000000000000), (277326545807/171734000000), (-1807449270526273605046208110010026121/84560133455117822502351000000000000), (277326545807/171734000000), (-3625594172047899782273694424737106121/169120266910235645004702000000000000)]
    bernstein := [(39083043042053121571617590201231949546679/432947883290203251212037120000000000000000), (132566612640823985757430592778896407343/1414862363693474677163520000000000000000), (30814190602709901928699883232174490532437/324710912467652438409027840000000000000000), (564482784885346969477573798232638647631/6013165045697267377944960000000000000000), (144236700225897429689843270953369566887/1591720159155159011808960000000000000000)]
    reserve := (22567983671/250000000000) }

theorem quarter_045_016_valid : quarter_045_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_045_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_045_016]
  · intro i; fin_cases i <;> norm_num [quarter_045_016]
  · norm_num [quarter_045_016]
  · norm_num [quarter_045_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_045_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_045_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_045_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_045_016]

def quarter_045_017 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 1]
    lambda := ![0, (707019/5000000), (7015169/50000000), (11971547/50000000), (11971547/50000000), (11971547/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (837699/20000000), 0, 0], ![(176067/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3126423/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1837867/50000000), (1113/1250000), (3506071/50000000), (1/100000000), (1/100000000), (6252847/100000000)]
    alternative := .zero
    polynomial := [(4552556854495815621769663593186239/358754815991095706496216000000000000), (41494238091/14840000000), (-3992241832302755695708224280174193761/179377407995547853248108000000000000), (41494238091/14840000000), (-7989036221460007207038218223941573761/358754815991095706496216000000000000)]
    bernstein := [(5571625729644877757690739691468369657439/57400770558575313039394560000000000000000), (11559646644885754554241792410900921236717/114801541117150626078789120000000000000000), (70265480654278814365274242772031118725653/688809246702903756472734720000000000000000), (46385233956361765318393525011037865296453/459206164468602504315156480000000000000000), (89712718342468249230432741779165596048559/918412328937205008630312960000000000000000)]
    reserve := (97065347301/1000000000000) }

theorem quarter_045_017_valid : quarter_045_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_045_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_045_017]
  · intro i; fin_cases i <;> norm_num [quarter_045_017]
  · norm_num [quarter_045_017]
  · norm_num [quarter_045_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_045_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_045_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_045_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_045_017]

def quarter_045_018 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 3, 0, 2, 0, 0, 1]
    lambda := ![0, (1835777/12500000), (7231521/50000000), (11808457/50000000), (11808457/50000000), (11808457/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (135943/3125000), 0, 0], ![(15941/625000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6167663/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1908811/50000000), (92161/100000000), (6997631/100000000), (1/100000000), (1/100000000), (6167663/100000000)]
    alternative := .zero
    polynomial := [(-1591810885660722364134845266791501/22330727085252137143286950000000000), (29264121157/7200078125), (-258924671906658095465740097544723501/11165363542626068571643475000000000), (29264121157/7200078125), (-516257532927655468567345349822655501/22330727085252137143286950000000000)]
    bernstein := [(5950326015810434104566147275631967115619/57166661338245471086814592000000000000000), (1542559115522455069720652923718478253073/14291665334561367771703648000000000000000), (390803319728609306725225888790885021391/3572916333640341942925912000000000000000), (96836481528457633204368287764539942797/893229083410085485731478000000000000000), (23449703720135078164813783212152834299/223307270852521371432869500000000000000)]
    reserve := (20817469051/200000000000) }

theorem quarter_045_018_valid : quarter_045_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_045_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_045_018]
  · intro i; fin_cases i <;> norm_num [quarter_045_018]
  · norm_num [quarter_045_018]
  · norm_num [quarter_045_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_045_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_045_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_045_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_045_018]

def quarter_045_019 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 3, 0, 2, 0, 0, 1]
    lambda := ![0, (15248507/100000000), (14867353/100000000), (11647357/50000000), (11647357/50000000), (11647357/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (4516731/100000000), 0, 0], ![(1694017/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6083519/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (990947/25000000), (47623/50000000), (174569/2500000), (1/100000000), (1/100000000), (6083519/100000000)]
    alternative := .zero
    polynomial := [(-154120959554136964273373376357747201/801879577668533128337456000000000000), (25831230082619/4762300000000), (-9697306949998744309730507266318027201/400939788834266564168728000000000000), (25831230082619/4762300000000), (-19240492940443351655187641156278307201/801879577668533128337456000000000000)]
    bernstein := [(893064862362636145970982832908761042599/8018795776685331283374560000000000000000), (740655950869843575220207199780942148619/6415036621348265026699648000000000000000), (1801975630401492570267423967239421813913/15396087891235836064079155200000000000000), (7333897751811574123263360399715212719/63163437502505994109042688000000000000), (1138323570559680292292608497355062387/10106150000400959057446830080000000000)]
    reserve := (111371443697/1000000000000) }

theorem quarter_045_019_valid : quarter_045_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_045_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_045_019]
  · intro i; fin_cases i <;> norm_num [quarter_045_019]
  · norm_num [quarter_045_019]
  · norm_num [quarter_045_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_045_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_045_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_045_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_045_019]

def quarter_045_020 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 3, 0, 2, 0, 0, 1]
    lambda := ![0, (989449/6250000), (609747/4000000), (22975047/100000000), (22975047/100000000), (22975047/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (187573/4000000), 0, 0], ![(4272793/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1500009/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1028813/25000000), (98309/100000000), (3483463/50000000), (1/100000000), (1/100000000), (6000037/100000000)]
    alternative := .zero
    polynomial := [(-11969266887241621585574841420048261559/33823211006899659476982832000000000000), (4227710761057/614431250000), (-427109321673911431078645744898736261559/16911605503449829738491416000000000000), (4227710761057/614431250000), (-842249376460581240571716648377424261559/33823211006899659476982832000000000000)]
    bernstein := [(659187604822742692769211114578171604529/5541594891370440208708867194880000000000), (8540662517531311638735278508190556540479/69269936142130502608860839936000000000000), (324788243931837206228924038752936265811843/2597622605329893847832281497600000000000000), (268731557527590298597698778790679203286147/2164685504441578206526901248000000000000000), (652629026935734347985243375933868332548921/5411713761103945516317253120000000000000000)]
    reserve := (59476343701/500000000000) }

theorem quarter_045_020_valid : quarter_045_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_045_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_045_020]
  · intro i; fin_cases i <;> norm_num [quarter_045_020]
  · norm_num [quarter_045_020]
  · norm_num [quarter_045_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_045_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_045_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_045_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_045_020]

def quarter_045_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 1]
    lambda := ![0, (4109491/25000000), (1949021/12500000), (22656623/100000000), (22656623/100000000), (22656623/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2434529/50000000), 0, 0], ![(5204897/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2958439/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2136491/50000000), (101361/100000000), (1389913/20000000), (1/100000000), (1/100000000), (5916879/100000000)]
    alternative := .zero
    polynomial := [(-3657968688948823748785563242909/6526144425802508652600000000000), (21389477377427/2534025000000), (-86168679587111664267459326858909/3263072212901254326300000000000), (21389477377427/2534025000000), (-168679390485274504786133090474909/6526144425802508652600000000000)]
    bernstein := [(132472620986684475968581992191067571/1044183108128401384416000000000000000), (274598371391834458361504136588901799/2088366216256802768832000000000000000), (1671444983377037335437735342737144593/12530197297540816612992000000000000000), (11415050234723164610509629701095087/86118194484816609024000000000000000), (22205529737011781771336332668556003/172236388969633218048000000000000000)]
    reserve := (63433616171/500000000000) }

theorem quarter_045_021_valid : quarter_045_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_045_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_045_021]
  · intro i; fin_cases i <;> norm_num [quarter_045_021]
  · norm_num [quarter_045_021]
  · norm_num [quarter_045_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_045_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_045_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_045_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_045_021]

def quarter_045_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 3, 0, 2, 0, 0, 1]
    lambda := ![0, (8536209/50000000), (7956391/50000000), (22338267/100000000), (22338267/100000000), (22338267/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (1264247/25000000), 0, 0], ![(247389/4000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2916869/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2218953/50000000), (104413/100000000), (6930137/100000000), (1/100000000), (1/100000000), (5833739/100000000)]
    alternative := .zero
    polynomial := [(-15300194909293133807084503215892377977/18733610587899621679816254000000000000), (2111764208301/208826000000), (-259012842209925644874695767878864417977/9366805293949810839908127000000000000), (2111764208301/208826000000), (-502725489510558155942307032541836457977/18733610587899621679816254000000000000)]
    bernstein := [(6481626941659098252286207798863082184483623/47958043105023031500329610240000000000000000), (279910262042928834914241124351904788668963/1998251796042626312513733760000000000000000), (79896259638322647692007178936522918620289/562008317636988650394487620000000000000000), (2207000621759474261540910906731082194631/15611342156583018066513545000000000000000), (402953747212633267140627162982119101887/2927126654359315887471289687500000000000)]
    reserve := (5406081251/40000000000) }

theorem quarter_045_022_valid : quarter_045_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_045_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_045_022]
  · intro i; fin_cases i <;> norm_num [quarter_045_022]
  · norm_num [quarter_045_022]
  · norm_num [quarter_045_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_045_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_045_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_045_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_045_022]

def quarter_045_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 1]
    lambda := ![0, (8869011/50000000), (1620527/10000000), (22018903/100000000), (22018903/100000000), (22018903/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2627073/50000000), 0, 0], ![(144259/2000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1150067/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (4610927/100000000), (26869/25000000), (172703/2500000), (1/100000000), (1/100000000), (89849/1562500)]
    alternative := .zero
    polynomial := [(-1020150364793100951868817392002433/904677824612367279464000000000000), (1279434657849/107476000000), (-13118159699148202543114033517802433/452338912306183639732000000000000), (1279434657849/107476000000), (-25216169033503304134359249643602433/904677824612367279464000000000000)]
    bernstein := [(20333263324261331209768297661188823/141355910095682387416250000000000000), (337215561220260345448841851539689539/2261694561530918198660000000000000000), (4108479332074860014853100653509077889/27140334738371018383920000000000000000), (43611332267496978209982825291003316543/289496903875957529428480000000000000000), (340090750822030196228140950491465323487/2315975231007660235427840000000000000000)]
    reserve := (143844451289/1000000000000) }

theorem quarter_045_023_valid : quarter_045_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_045_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_045_023]
  · intro i; fin_cases i <;> norm_num [quarter_045_023]
  · norm_num [quarter_045_023]
  · norm_num [quarter_045_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_045_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_045_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_045_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_045_023]

def quarter_045_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 3, 0, 2, 0, 0, 1]
    lambda := ![0, (288097/1562500), (16469211/100000000), (21697527/100000000), (21697527/100000000), (21697527/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (5461547/100000000), 0, 0], ![(518157/6250000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2833203/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (4792937/100000000), (110559/100000000), (6883003/100000000), (1/100000000), (1/100000000), (5666407/100000000)]
    alternative := .zero
    polynomial := [(-123916360715537785117372946266585526363/82668781783276365034616172000000000000), (199039302972/14395703125), (-1259211932518029109139169169378213046363/41334390891638182517308086000000000000), (199039302972/14395703125), (-2394507504320520433160965392489840566363/82668781783276365034616172000000000000)]
    bernstein := [(32375919063131146934263623540206912966322757/211632081365187494488617400320000000000000000), (3356322275662000644281432265456833606821693/21163208136518749448861740032000000000000000), (1022721967364784667979908238663123991257263/6348962440955624834658522009600000000000000), (33948326995576091238131114899113437799101/211632081365187494488617400320000000000000), (3312349196519198967310331797650289441093/21163208136518749448861740032000000000000)]
    reserve := (1195172613/7812500000) }

theorem quarter_045_024_valid : quarter_045_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_045_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_045_024]
  · intro i; fin_cases i <;> norm_num [quarter_045_024]
  · norm_num [quarter_045_024]
  · norm_num [quarter_045_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_045_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_045_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_045_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_045_024]

def quarter_045_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 1]
    lambda := ![0, (19176407/100000000), (16704021/100000000), (21373191/100000000), (21373191/100000000), (21373191/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (5680207/100000000), 0, 0], ![(2354653/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (697713/12500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (4984829/100000000), (11367/10000000), (171357/2500000), (1/100000000), (1/100000000), (1116341/20000000)]
    alternative := .zero
    polynomial := [(-27993905640917799953622215998427161/14452187489772673810788000000000000), (107253644351/6750000000), (-231625891834590337272526088322581161/7226093744886336905394000000000000), (107253644351/6750000000), (-435257878028262874591429960646735161/14452187489772673810788000000000000)]
    bernstein := [(601590012419428338391556850171682471/3699759997381804495561728000000000000), (693081228128458079680268147744814997/4110844441535338328401920000000000000), (190152893584209116206845782341423709021/1109927999214541348668518400000000000000), (23392370794098981625983322303651011487/137028148051177944280064000000000000000), (685307841259695126265813889643802116511/4110844441535338328401920000000000000000)]
    reserve := (162602442549/1000000000000) }

theorem quarter_045_025_valid : quarter_045_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_045_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_045_025]
  · intro i; fin_cases i <;> norm_num [quarter_045_025]
  · norm_num [quarter_045_025]
  · norm_num [quarter_045_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_045_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_045_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_045_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_045_025]

def quarter_045_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 3, 0, 2, 0, 0, 1]
    lambda := ![0, (9978043/50000000), (105681/625000), (4208997/20000000), (4208997/20000000), (4208997/20000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2955577/50000000), 0, 0], ![(10598701/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (686999/12500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (5187503/100000000), (116819/100000000), (1705361/25000000), (1/100000000), (1/100000000), (686999/12500000)]
    alternative := .zero
    polynomial := [(-1738598349370312136611098353688143743/709976995233981122436523000000000000), (105754294322143/5840950000000), (-11992592387124860023041547766505743743/354988497616990561218261500000000000), (105754294322143/5840950000000), (-22246586424879407909471997179323343743/709976995233981122436523000000000000)]
    bernstein := [(313966703084916390667922783399118533689137/1817541107798991673437498880000000000000000), (81405700949171338722191340681273050972601/454385276949747918359374720000000000000000), (62066068461333315574695105550844199231719/340788957712310938769531040000000000000000), (5156862823350355446452987535647648111629/28399079809359244897460920000000000000000), (1259941240353222833519338386729900389417/7099769952339811224365230000000000000000)]
    reserve := (17274255957/100000000000) }

theorem quarter_045_026_valid : quarter_045_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_045_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_045_026]
  · intro i; fin_cases i <;> norm_num [quarter_045_026]
  · norm_num [quarter_045_026]
  · norm_num [quarter_045_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_045_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_045_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_045_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_045_026]

def quarter_045_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 1]
    lambda := ![0, (20780791/100000000), (17083141/100000000), (20712023/100000000), (20712023/100000000), (20712023/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (3077719/50000000), 0, 0], ![(11832479/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5409037/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2700941/50000000), (120013/100000000), (6783983/100000000), (1/100000000), (1/100000000), (2704519/50000000)]
    alternative := .zero
    polynomial := [(-4523242654036506708559139827735728081/1486819286505370588458060250000000000), (245888273110889/12001300000000), (-26513468931055923707208328489484186831/743409643252685294229030125000000000), (245888273110889/12001300000000), (-48503695208075340705857517151232645581/1486819286505370588458060250000000000)]
    bernstein := [(2727402476764377161471909907177502877139/14868192865053705884580602500000000000000), (11317861502551057127240398142532798847319/59472771460214823538322410000000000000000), (138123229857832983066144574225081978581697/713673257522577882459868920000000000000000), (183719971366456065932057496464484869436879/951564343363437176613158560000000000000000), (718685193318823592692320698962939132096259/3806257373453748706452634240000000000000000)]
    reserve := (183438734049/1000000000000) }

theorem quarter_045_027_valid : quarter_045_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_045_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_045_027]
  · intro i; fin_cases i <;> norm_num [quarter_045_027]
  · norm_num [quarter_045_027]
  · norm_num [quarter_045_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_045_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_045_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_045_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_045_027]

def quarter_045_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 3, 0, 2, 0, 0, 1]
    lambda := ![0, (21654179/100000000), (269149/1562500), (5093357/25000000), (5093357/25000000), (5093357/25000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (6414143/100000000), 0, 0], ![(820119/6250000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1330153/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1407229/25000000), (123261/100000000), (52667/781250), (1/100000000), (1/100000000), (1330153/25000000)]
    alternative := .zero
    polynomial := [(-724413353205115310751639663562269407/194424336293084917347504000000000000), (5919667875767/256793750000), (-3666188060313258857935027888120349407/97212168146542458673752000000000000), (5919667875767/256793750000), (-2202654255807134135039472037559476469/64808112097694972449168000000000000)]
    bernstein := [(96920319096096634255217207248226707681073/497726300910297388409610240000000000000000), (4571810944416875887480780421211376700377/22623922768649881291345920000000000000000), (76749460564675741458165648638022866461499/373294725682723041307207680000000000000000), (1160654030080663687748793581057311296817/5655980692162470322836480000000000000000), (6246685632550544303933531426890775519393/31107893806893586775600640000000000000000)]
    reserve := (97363067733/500000000000) }

theorem quarter_045_028_valid : quarter_045_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_045_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_045_028]
  · intro i; fin_cases i <;> norm_num [quarter_045_028]
  · norm_num [quarter_045_028]
  · norm_num [quarter_045_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_045_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_045_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_045_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_045_028]

def quarter_045_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 3, 0, 2, 0, 0, 1]
    lambda := ![0, (11290031/50000000), (17334977/100000000), (125177/625000), (125177/625000), (125177/625000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (6688397/100000000), 0, 0], ![(7234601/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1046097/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1173919/20000000), (126571/100000000), (209159/3125000), (1/100000000), (1/100000000), (2615243/50000000)]
    alternative := .zero
    polynomial := [(-62386849797067678113611734612619171/13834169016468917226232000000000000), (81678869562631/3164275000000), (-276299894935598766962914202305659171/6917084508234458613116000000000000), (81678869562631/3164275000000), (-490212940074129855812216669998699171/13834169016468917226232000000000000)]
    bernstein := [(457387009835364416708864136835045227229/2213467042635026756197120000000000000000), (189931381870719943044893227994791952001/885386817054010702478848000000000000000), (77328644186549218486349150148576249957/354154726821604280991539200000000000000), (30886910388815995090917484460883533577/141661890728641712396615680000000000000), (12096100169433200142549235911798037741/56664756291456684958646272000000000000)]
    reserve := (103319137133/500000000000) }

theorem quarter_045_029_valid : quarter_045_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_045_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_045_029]
  · intro i; fin_cases i <;> norm_num [quarter_045_029]
  · norm_num [quarter_045_029]
  · norm_num [quarter_045_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_045_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_045_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_045_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_045_029]

def quarterTable045 : OwnerTable where
  mode := .quarter
  owners := ![0, 3, 0, 2, 0, 0, 1]
  rows := [quarter_045_000, quarter_045_001, quarter_045_002, quarter_045_003, quarter_045_004, quarter_045_005, quarter_045_006, quarter_045_007, quarter_045_008, quarter_045_009, quarter_045_010, quarter_045_011, quarter_045_012, quarter_045_013, quarter_045_014, quarter_045_015, quarter_045_016, quarter_045_017, quarter_045_018, quarter_045_019, quarter_045_020, quarter_045_021, quarter_045_022, quarter_045_023, quarter_045_024, quarter_045_025, quarter_045_026, quarter_045_027, quarter_045_028, quarter_045_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_045_000_valid
    · exact quarter_045_001_valid
    · exact quarter_045_002_valid
    · exact quarter_045_003_valid
    · exact quarter_045_004_valid
    · exact quarter_045_005_valid
    · exact quarter_045_006_valid
    · exact quarter_045_007_valid
    · exact quarter_045_008_valid
    · exact quarter_045_009_valid
    · exact quarter_045_010_valid
    · exact quarter_045_011_valid
    · exact quarter_045_012_valid
    · exact quarter_045_013_valid
    · exact quarter_045_014_valid
    · exact quarter_045_015_valid
    · exact quarter_045_016_valid
    · exact quarter_045_017_valid
    · exact quarter_045_018_valid
    · exact quarter_045_019_valid
    · exact quarter_045_020_valid
    · exact quarter_045_021_valid
    · exact quarter_045_022_valid
    · exact quarter_045_023_valid
    · exact quarter_045_024_valid
    · exact quarter_045_025_valid
    · exact quarter_045_026_valid
    · exact quarter_045_027_valid
    · exact quarter_045_028_valid
    · exact quarter_045_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
