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

def quarter_041_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 3, 0, 0, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(64079547/100000000), 0, (19192791/25000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (560543/100000000)]
    alternative := .zero
    polynomial := [(-519393814501857258543526403/25500310721794000000000000), (-64079547/560543), (-2265636775767813258543526403/12750155360897000000000000), (-64079547/560543), (-4011879737033769258543526403/25500310721794000000000000)]
    bernstein := [(44871879381266837221547798413/104449272716468224000000000000), (118565569597822284864385637161/261123181791170560000000000000), (900041480821549954429898111503/1958423863433779200000000000000), (728898063109215933426152754593/1632019886194816000000000000000), (1695751689872377268366533628797/4080049715487040000000000000000)]
    reserve := (20781017489/50000000000) }

theorem quarter_041_000_valid : quarter_041_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_041_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_041_000]
  · intro i; fin_cases i <;> norm_num [quarter_041_000]
  · norm_num [quarter_041_000]
  · norm_num [quarter_041_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_041_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_041_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_041_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_041_000]

def quarter_041_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(60597559/100000000), 0, (19887081/25000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (71153/12500000)]
    alternative := .zero
    polynomial := [(-3567884787796576400012997/202306469885875000000000), (-60597559/569224), (-17703919647340295150012997/101153234942937500000000), (-60597559/569224), (-31839954506884013900012997/202306469885875000000000)]
    bernstein := [(12501935583001258430979791803/32369035181740000000000000000), (26592731454965382940325433177/64738070363480000000000000000), (53950080917615703513363529043/129476140726960000000000000000), (104718388261650603138289401537/258952281453920000000000000000), (193849761346793175966427695083/517904562907840000000000000000)]
    reserve := (74859259883/200000000000) }

theorem quarter_041_001_valid : quarter_041_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_041_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_041_001]
  · intro i; fin_cases i <;> norm_num [quarter_041_001]
  · norm_num [quarter_041_001]
  · norm_num [quarter_041_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_041_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_041_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_041_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_041_001]

def quarter_041_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 3, 0, 0, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(28469751/50000000), 0, (41103203/50000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (577517/100000000)]
    alternative := .zero
    polynomial := [(-198390637679986255814753033/13136247305843000000000000), (-56939502/577517), (-1133327340271023255814753033/6568123652921500000000000), (-56939502/577517), (-2068264042862060255814753033/13136247305843000000000000)]
    bernstein := [(11527812398842346443288633898087/33628793102958080000000000000000), (3089044506232968121565127349497/8407198275739520000000000000000), (2356369666203460441793466878321/6305398706804640000000000000000), (190236389246127754008252617917/525449892233720000000000000000), (43716866270860360664919214927/131362473058430000000000000000)]
    reserve := (41599462591/125000000000) }

theorem quarter_041_002_valid : quarter_041_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_041_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_041_002]
  · intro i; fin_cases i <;> norm_num [quarter_041_002]
  · norm_num [quarter_041_002]
  · norm_num [quarter_041_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_041_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_041_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_041_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_041_002]

def quarter_041_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(53110117/100000000), 0, (84730841/100000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (585377/100000000)]
    alternative := .zero
    polynomial := [(-340003764663742932710239531/26630062973566000000000000), (-53110117/585377), (-2267298167786181932710239531/13315031486783000000000000), (-53110117/585377), (-4194592570908620932710239531/26630062973566000000000000)]
    bernstein := [(79690490161174118469644132189/266300629735660000000000000000), (345095618111994513874824855393/1065202518942640000000000000000), (1408630571095557185999559254641/4260810075770560000000000000000), (5445712097213912795858473175517/17043240303082240000000000000000), (536280456569952094069498304417/1842512465198080000000000000000)]
    reserve := (291059337019/1000000000000) }

theorem quarter_041_003_valid : quarter_041_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_041_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_041_003]
  · intro i; fin_cases i <;> norm_num [quarter_041_003]
  · norm_num [quarter_041_003]
  · norm_num [quarter_041_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_041_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_041_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_041_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_041_003]

def quarter_041_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 3, 0, 0, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(24557813/50000000), 0, (21776787/25000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (592757/100000000)]
    alternative := .zero
    polynomial := [(-143343884427826251024359563/13482897549803000000000000), (-49115626/592757), (-1134016919364172251024359563/6741448774901500000000000), (-49115626/592757), (-2124689954300518251024359563/13482897549803000000000000)]
    bernstein := [(8820091375988401027759847564517/34516217727495680000000000000000), (967635282974101041790199845167/3451621772749568000000000000000), (297494973461131953373716301943/1035486531824870400000000000000), (9552729943284566272186750359/34516217727495680000000000000), (859512033393321453960086293/3451621772749568000000000000)]
    reserve := (249016865109/1000000000000) }

theorem quarter_041_004_valid : quarter_041_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_041_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_041_004]
  · intro i; fin_cases i <;> norm_num [quarter_041_004]
  · norm_num [quarter_041_004]
  · norm_num [quarter_041_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_041_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_041_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_041_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_041_004]

def quarter_041_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(44963763/100000000), 0, (44660553/50000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (299807/50000000)]
    alternative := .zero
    polynomial := [(-118578646771640548454882503/13638867413506000000000000), (-44963763/599614), (-1134431113493327548454882503/6819433706753000000000000), (-44963763/599614), (-2150283580215014548454882503/13638867413506000000000000)]
    bernstein := [(738739977257359496538956633/3491550057857536000000000000), (8256344367311587289122568881/34915500578575360000000000000), (255293416136960765965024375403/1047465017357260800000000000000), (815898362708370707000884605233/3491550057857536000000000000000), (7213078694035214263582763440217/34915500578575360000000000000000)]
    reserve := (41317343727/200000000000) }

theorem quarter_041_005_valid : quarter_041_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_041_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_041_005]
  · intro i; fin_cases i <;> norm_num [quarter_041_005]
  · norm_num [quarter_041_005]
  · norm_num [quarter_041_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_041_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_041_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_041_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_041_005]

def quarter_041_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 3, 0, 0, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1270743/3125000), 0, (22839737/25000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (37869/6250000)]
    alternative := .zero
    polynomial := [(-1497850999510546586193607/215342816412750000000000), (-847162/12623), (-17732677941423765336193607/107671408206375000000000), (-847162/12623), (-11322501627778994695397869/71780938804250000000000)]
    bernstein := [(7094624971197313201035914621/42405970001280000000000000000), (13248595199800887356686246297/68909701252080000000000000000), (99284856039911855952429187/496944960952500000000000000), (34129240290295240728989927/179452347010625000000000000), (423635897820925629483109/2588255004960937500000000)]
    reserve := (163676259491/1000000000000) }

theorem quarter_041_006_valid : quarter_041_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_041_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_041_006]
  · intro i; fin_cases i <;> norm_num [quarter_041_006]
  · norm_num [quarter_041_006]
  · norm_num [quarter_041_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_041_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_041_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_041_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_041_006]

def quarter_041_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7245283/20000000), 0, (93207547/100000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (611587/100000000)]
    alternative := .zero
    polynomial := [(-150687422572205627852459171/27822412434746000000000000), (-36226415/611587), (-2270793650030418627852459171/13911206217373000000000000), (-36226415/611587), (-4390899877488631627852459171/27822412434746000000000000)]
    bernstein := [(533022964331504892934400101/4347251942929062500000000000), (10268426581741151949032370839/69556031086865000000000000000), (43235408984956686979468288849/278224124347460000000000000000), (1301485363751958291458029193347/8903171979118720000000000000000), (8559979570496087711965169757629/71225375832949760000000000000000)]
    reserve := (120181599189/1000000000000) }

theorem quarter_041_007_valid : quarter_041_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_041_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_041_007]
  · intro i; fin_cases i <;> norm_num [quarter_041_007]
  · norm_num [quarter_041_007]
  · norm_num [quarter_041_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_041_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_041_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_041_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_041_007]

def quarter_041_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 3, 0, 0, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7915969/25000000), 0, (4742731/5000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (616623/100000000)]
    alternative := .zero
    polynomial := [(-28580283563198360088284407/7012877735608500000000000), (-31663876/616623), (-189324317857314453362761469/1168812955934750000000000), (-31663876/616623), (-1107365623580688360088284407/7012877735608500000000000)]
    bernstein := [(1389602794071461999576952201193/17952967003157760000000000000000), (919762875047625900038009555597/8976483501578880000000000000000), (495671228434459756387585433713/4488241750789440000000000000000), (227903837404947184315067257877/2244120875394720000000000000000), (85262884701077516071696112633/1122060437697360000000000000000)]
    reserve := (37993891343/500000000000) }

theorem quarter_041_008_valid : quarter_041_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_041_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_041_008]
  · intro i; fin_cases i <;> norm_num [quarter_041_008]
  · norm_num [quarter_041_008]
  · norm_num [quarter_041_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_041_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_041_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_041_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_041_008]

def quarter_041_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 3, 0, 0, 0, 2, 1]
    lambda := ![0, 0, 0, (3/100000000), (1/100000000), 0, (24999999/25000000)]
    cone := fun i => (![![0, 0, (49098429/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(6747431/25000000), 0, (24072227/25000000), 0, 0]] i.1) i.2
    mu := ![(11373039/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (31049/5000000)]
    alternative := .zero
    polynomial := [(-230215652120983324765049/78471441758000000000000), (-168685768252569/3881125000000), (-6314090441829382002229049/39235720879000000000000), (-168685768252569/3881125000000), (-12397965231537780679693049/78471441758000000000000)]
    bernstein := [(396252690095703697007230231/12555430681280000000000000000), (284500036813379005709438317/5022172272512000000000000000), (390461754441762070127470573/6026606727014400000000000000), (9029196583470922739584369/160709512720384000000000000), (398156602392322793801119/12856761017630720000000000)]
    reserve := (7742163867/250000000000) }

theorem quarter_041_009_valid : quarter_041_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_041_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_041_009]
  · intro i; fin_cases i <;> norm_num [quarter_041_009]
  · norm_num [quarter_041_009]
  · norm_num [quarter_041_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_041_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_041_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_041_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_041_009]

def quarter_041_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 3, 0, 0, 0, 2, 1]
    lambda := ![(1177013/12500000), (970613/5000000), (21443701/100000000), (21443701/100000000), (3344567/50000000), (3565067/50000000), (14464967/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(3213941/100000000), 0, (1394653/20000000), 0, 0]] i.1) i.2
    mu := ![(4361189/100000000), (2725839/50000000), (689027/50000000), (1/100000000), (5675897/100000000), (247037/10000000), (5647/6250000)]
    alternative := .zero
    polynomial := [(-1399632373643413318830726760517959980459797851/5294434243209659895286120771971756000000000000), (-49997423535987/9035200000000), (-69167463707269971374434443638865536821859024101/2647217121604829947643060385985878000000000000), (-49997423535987/9035200000000), (-136935295040896529430038160517213113663258250351/5294434243209659895286120771971756000000000000)]
    bernstein := [(20455792697414647444092825671242197955985174681/867440106407470677243678027279852503040000000000), (348014428361159453198526924525393739946447033/11811548289862073491880147430281216000000000000), (3312662985619867952220767843275601157534588977363/101653137469625469989493518821857715200000000000000), (512283401818105527592123338729456179763102697/15531893636111946887528040401824000000000000000), (945628941603926716186494228016003446655878797/30835377071692835732592433150680000000000000000)]
    reserve := (23581792617/1000000000000) }

theorem quarter_041_010_valid : quarter_041_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_041_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_041_010]
  · intro i; fin_cases i <;> norm_num [quarter_041_010]
  · norm_num [quarter_041_010]
  · norm_num [quarter_041_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_041_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_041_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_041_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_041_010]

def quarter_041_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 1]
    lambda := ![(554239/6250000), (5097563/25000000), (1382987/6250000), (1382987/6250000), (854281/12500000), (1814277/25000000), (2478997/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(2152641/100000000), 0, (61869/1250000), 0, 0]] i.1) i.2
    mu := ![(3850979/100000000), (5618371/100000000), (577417/50000000), (1/100000000), (2925927/50000000), (2518861/100000000), (77783/100000000)]
    alternative := .zero
    polynomial := [(-159383533184863030745228600614771787513757382783/1302149410653905495453026887484342446000000000000), (-29853982848017/7778300000000), (-15367613120198434437145355791939454653760975662783/651074705326952747726513443742171223000000000000), (-29853982848017/7778300000000), (-30575842707212005843545482983264137520008193942783/1302149410653905495453026887484342446000000000000)]
    bernstein := [(3463750532311975675543015583831876725195783178917/128925684223158959945844246285578460000000000000000), (1679760245912328794191966873359528080213274492953551/52085976426156219818121075499373697840000000000000000), (21968461400942968951219910420010857472928178404488959/625031717113874637817452905992484374080000000000000000), (29653118596912413885070427136001454032411943689797659/833375622818499517089937207989979165440000000000000000), (111888446067814131962549463897174745175305482221204177/3333502491273998068359748831959916661760000000000000000)]
    reserve := (839570523/31250000000) }

theorem quarter_041_011_valid : quarter_041_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_041_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_041_011]
  · intro i; fin_cases i <;> norm_num [quarter_041_011]
  · norm_num [quarter_041_011]
  · norm_num [quarter_041_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_041_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_041_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_041_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_041_011]

def quarter_041_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 3, 0, 0, 0, 2, 1]
    lambda := ![(1661627/20000000), (10687593/50000000), (11364787/50000000), (11364787/50000000), (3465053/50000000), (1464581/20000000), (10604519/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1320407/100000000), 0, (3199089/100000000), 0, 0]] i.1) i.2
    mu := ![(136159/4000000), (5794717/100000000), (900649/100000000), (1/100000000), (6004327/100000000), (1273789/50000000), (2671/4000000)]
    alternative := .zero
    polynomial := [(-992644567797024734430282550394986811309147529/29033531814730098814753157700220622000000000000), (-16856937209533/6677500000000), (-321876753709730859960496667889553036282730757929/14516765907365049407376578850110311000000000000), (-16856937209533/6677500000000), (-642760862851664695186563053228711085754152368329/29033531814730098814753157700220622000000000000)]
    bernstein := [(2288198047326557063448997560494479959459998130962151/74325841445709052965768083712564792320000000000000000), (120821727887372859253113923221642680050470716632647/3378447338441320589353094714207490560000000000000000), (2141177348756881160896970264908819916532043832105917/55744381084281789724326062784423594240000000000000000), (32725781258624975437041591561222332022755598917183/844611834610330147338273678551872640000000000000000), (170845466180021559549544951889784294603080683896471/4645365090356815810360505232035299520000000000000000)]
    reserve := (15393018113/500000000000) }

theorem quarter_041_012_valid : quarter_041_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_041_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_041_012]
  · intro i; fin_cases i <;> norm_num [quarter_041_012]
  · norm_num [quarter_041_012]
  · norm_num [quarter_041_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_041_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_041_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_041_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_041_012]

def quarter_041_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 1]
    lambda := ![(9032563/100000000), (26117509/100000000), (27146311/100000000), (27146311/100000000), 0, 0, (5278653/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8040957/100000000), 0, 0], ![0, 0, 0, 0, 0], ![(395343/50000000), 0, (2105531/20000000), 0, 0]] i.1) i.2
    mu := ![(1755371/50000000), (1396579/20000000), (360251/50000000), (1/100000000), (7056573/100000000), (1/100000000), (66623/100000000)]
    alternative := .zero
    polynomial := [(18600200533313033501846655716571938841907/1660801148350327477249175551044000000000000), (-69573927389/39190000000), (-22005912150066808109793386790458094954248093/830400574175163738624587775522000000000000), (-69573927389/39190000000), (-44030424500666929253088620236632761847338093/1660801148350327477249175551044000000000000)]
    bernstein := [(8973575518045833599568361625318713802187307507/265728183736052396359868088167040000000000000000), (6950828752417542347811166919376968139658396769/177152122490701597573245392111360000000000000000), (133700925244099692039055525431179598686505342121/3188738204832628756318417058004480000000000000000), (29663302628503570941772425772840093199757399569/708608489962806390292981568445440000000000000000), (165970182650138227157619164733578335112496684307/4251650939776838341757889410672640000000000000000)]
    reserve := (1688487723/50000000000) }

theorem quarter_041_013_valid : quarter_041_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_041_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_041_013]
  · intro i; fin_cases i <;> norm_num [quarter_041_013]
  · norm_num [quarter_041_013]
  · norm_num [quarter_041_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_041_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_041_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_041_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_041_013]

def quarter_041_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 3, 0, 0, 0, 2, 1]
    lambda := ![(8342223/100000000), (683143/2500000), (27696519/100000000), (27696519/100000000), 0, 0, (8939019/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8203933/100000000), 0, 0], ![0, 0, 0, 0, 0], ![(223441/100000000), 0, (357449/4000000), 0, 0]] i.1) i.2
    mu := ![(3089511/100000000), (7219257/100000000), (35987/10000000), (1/100000000), (7199597/100000000), (1/100000000), (3529/6250000)]
    alternative := .zero
    polynomial := [(21978187132723132686682510023438881423/566480855519547606545445998250000000000), (-5083182252539/5646400000000), (-79534454542024101395711594495425697265491/2265923422078190426181783993000000000000), (-5083182252539/5646400000000), (-79622367290554993926458324535519452791183/2265923422078190426181783993000000000000)]
    bernstein := [(228357200158517171965472592180336936643018217/5800763960520167491025367022080000000000000000), (5187295194684479758643362010502599754127919/116015279210403349820507340441600000000000000), (1009216151630549335211201660593645636602709/21752864851950628091345126332800000000000000), (3221188320115236219625869399981873967519/72509549506502093637817087776000000000000), (21978187132723132686682510023438881423/566480855519547606545445998250000000000)]
    reserve := (38797757979/1000000000000) }

theorem quarter_041_014_valid : quarter_041_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_041_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_041_014]
  · intro i; fin_cases i <;> norm_num [quarter_041_014]
  · norm_num [quarter_041_014]
  · norm_num [quarter_041_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_041_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_041_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_041_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_041_014]

def quarter_041_015 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 1]
    lambda := ![0, (16670139/50000000), (33329861/100000000), (33329861/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (493783/5000000), 0, 0], ![(833377/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (394903/4000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (8666669/100000000), (42119/20000000), (1/100000000), (4331981/50000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(10865412768161549313723941887/230008614711512929600000000000), (13892510429403/10529750000000), (-6057458719573314605076884125313/115004307355756464800000000000), (13892510429403/10529750000000), (-12125782851914790759467492192513/230008614711512929600000000000)]
    bernstein := [(10865412768161549313723941887/230008614711512929600000000000), (12762061002172464620690561767/230008614711512929600000000000), (835121371611778039580228412731/14338199358639767040000000000000), (20433009880971568685628164937767/368013783538420687360000000000000), (2532116315088771574311869861450717/53529277605588463616000000000000000)]
    reserve := (47239155723/1000000000000) }

theorem quarter_041_015_valid : quarter_041_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_041_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_041_015]
  · intro i; fin_cases i <;> norm_num [quarter_041_015]
  · norm_num [quarter_041_015]
  · norm_num [quarter_041_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_041_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_041_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_041_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_041_015]

def quarter_041_016 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 3, 0, 0, 0, 2, 1]
    lambda := ![0, (33395863/100000000), (33302069/100000000), (33302069/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (79137/800000), 0, 0], ![(625293/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4932171/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (8681119/100000000), (52687/25000000), (1/100000000), (8656737/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1641884147243693832309393073/833565619628213676000000000000), (1099063124361/277300000000), (-21995945882204080461362430588073/416782809814106838000000000000), (1099063124361/277300000000), (-43990249880260917228892551783073/833565619628213676000000000000)]
    bernstein := [(136940532833435394509548573832303327/2133927986248227010560000000000000000), (25777133053688872417640319666533909/355654664374704501760000000000000000), (120506983682288843534064657245311181/1600445989686170257920000000000000000), (6457046677331210329069685740723109/88913666093676125440000000000000000), (8592955110668920369672673672478527/133370499140514188160000000000000000)]
    reserve := (64172986959/1000000000000) }

theorem quarter_041_016_valid : quarter_041_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_041_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_041_016]
  · intro i; fin_cases i <;> norm_num [quarter_041_016]
  · norm_num [quarter_041_016]
  · norm_num [quarter_041_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_041_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_041_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_041_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_041_016]

def quarter_041_017 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 1]
    lambda := ![0, (33507171/100000000), (6649283/20000000), (6649283/20000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (1985019/20000000), 0, 0], ![(4172099/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9847857/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (8710053/100000000), (210989/100000000), (1/100000000), (864227/10000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-502354664585921049564789107909/4235231694474204424000000000000), (139795234621929/21098900000000), (-112309600177623056401467601307909/2117615847237102212000000000000), (139795234621929/21098900000000), (-224116845690660191753370413507909/4235231694474204424000000000000)]
    bernstein := [(54604088399840264026189195487524891/677637071115872707840000000000000000), (10963999278845591712812430876179843/123206740202885946880000000000000000), (747244496163463772311707478680953257/8131644853390472494080000000000000000), (43999089545395384560154390178732587/492826960811543787520000000000000000), (879402125597597061099121676482240171/10842193137853963325440000000000000000)]
    reserve := (1611602751/20000000000) }

theorem quarter_041_017_valid : quarter_041_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_041_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_041_017]
  · intro i; fin_cases i <;> norm_num [quarter_041_017]
  · norm_num [quarter_041_017]
  · norm_num [quarter_041_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_041_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_041_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_041_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_041_017]

def quarter_041_018 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 3, 0, 0, 0, 2, 1]
    lambda := ![0, (16837241/50000000), (33162759/100000000), (33162759/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (4987327/50000000), 0, 0], ![(5848259/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4911539/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1094193/12500000), (211319/100000000), (1/100000000), (2155131/25000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-134627794245424826661206512079/442948903009626024000000000000), (98468546213419/10565950000000), (-11838691220909077208893802752079/221474451504813012000000000000), (98468546213419/10565950000000), (-23542754647572729591126398992079/442948903009626024000000000000)]
    bernstein := [(109531169316043217448279260337926401/1133949191704642621440000000000000000), (29808202035797643574485546801190267/283487297926160655360000000000000000), (22998051598270191562069117530317167/212615473444620491520000000000000000), (1871440976126372745869457149008463/17717956120385040960000000000000000), (431749059553815624883857934602121/4429489030096260240000000000000000)]
    reserve := (19318532103/200000000000) }

theorem quarter_041_018_valid : quarter_041_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_041_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_041_018]
  · intro i; fin_cases i <;> norm_num [quarter_041_018]
  · norm_num [quarter_041_018]
  · norm_num [quarter_041_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_041_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_041_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_041_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_041_018]

def quarter_041_019 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 3, 0, 0, 0, 2, 1]
    lambda := ![0, (4237277/12500000), (8262723/25000000), (8262723/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (5020463/50000000), 0, 0], ![(301271/4000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4894971/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (8811703/100000000), (211737/100000000), (1/100000000), (1718289/20000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-398856997773311486740558744873/712426888556220462000000000000), (1276568679067/105868500000), (-19247217465244228275575270104873/356213444278110231000000000000), (1276568679067/105868500000), (-38095577932715145064409981464873/712426888556220462000000000000)]
    bernstein := [(800281667849622926243993388830527/7124268885562204620000000000000000), (230023963691490043405185212891329/1899805036149921232000000000000000), (1699398227188068548568147131285249/13678596260279432870400000000000000), (29612787328011806333208409045577/243175044627189917696000000000000), (4421266263846078582487873414821/38908007140350386831360000000000)]
    reserve := (28082940183/250000000000) }

theorem quarter_041_019_valid : quarter_041_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_041_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_041_019]
  · intro i; fin_cases i <;> norm_num [quarter_041_019]
  · norm_num [quarter_041_019]
  · norm_num [quarter_041_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_041_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_041_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_041_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_041_019]

def quarter_041_020 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 3, 0, 0, 0, 2, 1]
    lambda := ![0, (1708947/5000000), (3291053/10000000), (3291053/10000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (10124079/100000000), 0, 0], ![(4612401/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1949673/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2221169/25000000), (42449/20000000), (1/100000000), (4277479/50000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-337442807510334332325344389521/379584101937898352000000000000), (7882348851747/530612500000), (-10395961260017558030662217989521/189792050968949176000000000000), (7882348851747/530612500000), (-20454479712524781728999091589521/379584101937898352000000000000)]
    bernstein := [(7954774143804130540935625434951/62191059261505265991680000000000), (106414909511493600727779600077001/777388240768815824896000000000000), (1362519324658474023100045959352439/9717353009610197811200000000000000), (3348683706567641559905159912123493/24293382524025494528000000000000000), (7877409083534635929990491512537599/60733456310063736320000000000000000)]
    reserve := (63954322681/500000000000) }

theorem quarter_041_020_valid : quarter_041_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_041_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_041_020]
  · intro i; fin_cases i <;> norm_num [quarter_041_020]
  · norm_num [quarter_041_020]
  · norm_num [quarter_041_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_041_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_041_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_041_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_041_020]

def quarter_041_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 1]
    lambda := ![0, (17258683/50000000), (32741317/100000000), (32741317/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (10224323/100000000), 0, 0], ![(85387/781250), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9698243/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (8972649/100000000), (106421/50000000), (1/100000000), (2127743/25000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-6012198133711551225963951509447/4643967027386400336000000000000), (1473667165321/83141406250), (-129304395522991623624323400389447/2321983513693200168000000000000), (1473667165321/83141406250), (-252596592912271696022682849269447/4643967027386400336000000000000)]
    bernstein := [(15224297668399449863668274562405199/106147817768832007680000000000000000), (226894147838926295983238707416861317/1486069448763648107520000000000000000), (1392755120415949223152664679861445219/8916416692581888645120000000000000000), (914994914011538352069613367177837437/5944277795054592430080000000000000000), (1733157144156703846372358702032048153/11888555590109184860160000000000000000)]
    reserve := (71712720941/500000000000) }

theorem quarter_041_021_valid : quarter_041_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_041_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_041_021]
  · intro i; fin_cases i <;> norm_num [quarter_041_021]
  · norm_num [quarter_041_021]
  · norm_num [quarter_041_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_041_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_041_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_041_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_041_021]

def quarter_041_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 3, 0, 0, 0, 2, 1]
    lambda := ![0, (34914361/100000000), (32542819/100000000), (32542819/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2585479/25000000), 0, 0], ![(12648221/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9639447/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (4537923/50000000), (53383/25000000), (1/100000000), (8459373/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1084906244690857865820446053/609220576031381600000000000), (441604554001781/21353200000000), (-17293333200913729839346317053/304610288015690800000000000), (441604554001781/21353200000000), (-33501760157136601812872188053/609220576031381600000000000)]
    bernstein := [(247939312296245145766976149054347/1559604674640336896000000000000000), (32858999968443855434139242902321/194950584330042112000000000000000), (3148873672477164757451072749921/18276617280941448000000000000000), (19931374212420788902173400529/117157803082958000000000000000), (1185949137472181599175775311/7322362692684875000000000000)]
    reserve := (15897574323/100000000000) }

theorem quarter_041_022_valid : quarter_041_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_041_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_041_022]
  · intro i; fin_cases i <;> norm_num [quarter_041_022]
  · norm_num [quarter_041_022]
  · norm_num [quarter_041_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_041_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_041_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_041_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_041_022]

def quarter_041_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 1]
    lambda := ![0, (8842737/25000000), (16157263/50000000), (16157263/50000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (10477161/100000000), 0, 0], ![(14383163/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (598239/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (4597267/50000000), (107157/50000000), (1/100000000), (8400029/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-77873722197546883566566035225213/33104805932563661208000000000000), (42395509212377/1785950000000), (-960658830050364019988310264505213/16552402966281830604000000000000), (42395509212377/1785950000000), (-1843443937903181156410054493785213/33104805932563661208000000000000)]
    bernstein := [(903374143861895220207428397899003/5172625926963072063750000000000000), (1388769605769629120653550195052389/7523819530128104820000000000000000), (187274115021840695041040351573625629/993144177976909836240000000000000000), (179623453229712439315891613865881993/963048899856397416960000000000000000), (15112786586261557969312628737703527907/84748303187362972692480000000000000000)]
    reserve := (43661292959/250000000000) }

theorem quarter_041_023_valid : quarter_041_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_041_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_041_023]
  · intro i; fin_cases i <;> norm_num [quarter_041_023]
  · norm_num [quarter_041_023]
  · norm_num [quarter_041_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_041_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_041_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_041_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_041_023]

def quarter_041_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 3, 0, 0, 0, 2, 1]
    lambda := ![0, (35888317/100000000), (16027921/50000000), (16027921/50000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (1063041/10000000), 0, 0], ![(8068369/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (11869/125000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (4664511/50000000), (26899/12500000), (1/100000000), (4166393/50000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-5794096913512966776615734609/1921912384721911312500000000), (289560184344973/10759600000000), (-457339445150699468253631303747/7687649538887645250000000000), (289560184344973/10759600000000), (-434163057496647601147168365311/7687649538887645250000000000)]
    bernstein := [(3749340215277918525581340551498329/19680382819552371840000000000000000), (197647295239060906226489699135723/984019140977618592000000000000000), (2816279390548937428441861161427/13730499641548166400000000000000), (499833162188817794146192893859/2460047852444046480000000000000), (10369372086785850954094202233/53190223836628032000000000000)]
    reserve := (19051154897/100000000000) }

theorem quarter_041_024_valid : quarter_041_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_041_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_041_024]
  · intro i; fin_cases i <;> norm_num [quarter_041_024]
  · norm_num [quarter_041_024]
  · norm_num [quarter_041_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_041_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_041_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_041_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_041_024]

def quarter_041_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 1]
    lambda := ![0, (36467829/100000000), (15883043/50000000), (15883043/50000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (5401033/50000000), 0, 0], ![(17911403/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2352343/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (592479/6250000), (108083/50000000), (1/100000000), (1651493/20000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-6386805025936356762464391877439/1692104078437299216000000000000), (653189981754087/21616600000000), (-51726992056443817457429440597439/846052039218649608000000000000), (653189981754087/21616600000000), (-97067179086951278152394489317439/1692104078437299216000000000000)]
    bernstein := [(3086699134941805056539940106901/14937194623446503424000000000000), (104657924588572098994631481267203/481309604533276221440000000000000), (28848945801298878061541055775459579/129953593223984579788800000000000000), (10597933306593419549233002796342139/48130960453327622144000000000000000), (917912298990240571547668151719954801/4331786440799485992960000000000000000)]
    reserve := (206645170847/1000000000000) }

theorem quarter_041_025_valid : quarter_041_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_041_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_041_025]
  · intro i; fin_cases i <;> norm_num [quarter_041_025]
  · norm_num [quarter_041_025]
  · norm_num [quarter_041_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_041_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_041_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_041_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_041_025]

def quarter_041_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 3, 0, 0, 0, 2, 1]
    lambda := ![0, (9277757/25000000), (15722243/50000000), (15722243/50000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (10992587/100000000), 0, 0], ![(1970971/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9314111/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (9646861/100000000), (5431/2500000), (1/100000000), (4086933/50000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-118597833625114211294884972747/25566926683591272000000000000), (18286189992047/543100000000), (-805280715386472568798710484747/12783463341795636000000000000), (18286189992047/543100000000), (-1491963597147830926302535996747/25566926683591272000000000000)]
    bernstein := [(14602763282212854945483211658868773/65451332309993656320000000000000000), (3835572340589528190314924384712829/16362833077498414080000000000000000), (2936473009933712603670033916030451/12272124808123810560000000000000000), (242994689763121589147601747331841/1022677067343650880000000000000000), (58610962754307702238180617048893/255669266835912720000000000000000)]
    reserve := (223108724709/1000000000000) }

theorem quarter_041_026_valid : quarter_041_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_041_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_041_026]
  · intro i; fin_cases i <;> norm_num [quarter_041_026]
  · norm_num [quarter_041_026]
  · norm_num [quarter_041_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_041_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_041_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_041_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_041_026]

def quarter_041_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 1]
    lambda := ![0, (756393/2000000), (1243607/4000000), (1243607/4000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (11202487/100000000), 0, 0], ![(269179/1250000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4604581/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1228883/12500000), (43683/20000000), (1/100000000), (2020441/25000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-19490474642466906879295103037451/3470716529643367968000000000000), (67868370449/1820125000), (-112912087231596094705537223037451/1735358264821683984000000000000), (67868370449/1820125000), (-206333699820725282531779343037451/3470716529643367968000000000000)]
    bernstein := [(8328232418962804003142579292044669/34707165296433679680000000000000000), (34957625587007847844259144474932199/138828661185734718720000000000000000), (428189324206617640954910705134472387/1665943934228816624640000000000000000), (567502680411304651923314000642890459/2221258578971755499520000000000000000), (2194902829288820418259190353459301189/8885034315887021998080000000000000000)]
    reserve := (47991429711/200000000000) }

theorem quarter_041_027_valid : quarter_041_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_041_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_041_027]
  · intro i; fin_cases i <;> norm_num [quarter_041_027]
  · norm_num [quarter_041_027]
  · norm_num [quarter_041_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_041_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_041_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_041_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_041_027]

def quarter_041_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 3, 0, 0, 0, 2, 1]
    lambda := ![0, (9648909/25000000), (15351091/50000000), (15351091/50000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (571617/5000000), 0, 0], ![(11694007/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1818847/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (5016389/50000000), (13731/6250000), (1/100000000), (7980907/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-2952891921884274992970590175719/439780137854963690400000000000), (37611469796121/915400000000), (-14813061790412771300755979649719/219890068927481845200000000000), (37611469796121/915400000000), (-26673231658941267608541369123719/439780137854963690400000000000)]
    bernstein := [(289607216084096504557827853289266441/1125837152908707047424000000000000000), (4600269966678541350906261206909403/17058138680434955264000000000000000), (232438801164546206321781028624982083/844377864681530285568000000000000000), (1167965567649276431619821422774563/4264534670108738816000000000000000), (18668663250540358251881234838485881/70364822056794190464000000000000000)]
    reserve := (128618608533/500000000000) }

theorem quarter_041_028_valid : quarter_041_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_041_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_041_028]
  · intro i; fin_cases i <;> norm_num [quarter_041_028]
  · norm_num [quarter_041_028]
  · norm_num [quarter_041_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_041_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_041_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_041_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_041_028]

def quarter_041_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 3, 0, 0, 0, 2, 1]
    lambda := ![0, (19720573/50000000), (30279427/100000000), (30279427/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (11682787/100000000), 0, 0], ![(6318427/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8969011/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2050513/20000000), (44217/20000000), (1/100000000), (3935507/50000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-22680415425699938123471916482143/2854581696460229976000000000000), (124603000898671/2763562500000), (-33259901940493286369482729819381/475763616076704996000000000000), (124603000898671/2763562500000), (-10404646836309398829024968378479/167916570380013528000000000000)]
    bernstein := [(125595674631704441966965824124417057/456733071433636796160000000000000000), (52630386664879708104060371205200533/182693228573454718464000000000000000), (21490539329017527592283827192235081/73077291429381887385600000000000000), (8559427822631408010058551107844541/29230916571752754954240000000000000), (3322013469597050272138188119811953/11692366628701101981696000000000000)]
    reserve := (274987038353/1000000000000) }

theorem quarter_041_029_valid : quarter_041_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_041_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_041_029]
  · intro i; fin_cases i <;> norm_num [quarter_041_029]
  · norm_num [quarter_041_029]
  · norm_num [quarter_041_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_041_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_041_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_041_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_041_029]

def quarterTable041 : OwnerTable where
  mode := .quarter
  owners := ![0, 3, 0, 0, 0, 2, 1]
  rows := [quarter_041_000, quarter_041_001, quarter_041_002, quarter_041_003, quarter_041_004, quarter_041_005, quarter_041_006, quarter_041_007, quarter_041_008, quarter_041_009, quarter_041_010, quarter_041_011, quarter_041_012, quarter_041_013, quarter_041_014, quarter_041_015, quarter_041_016, quarter_041_017, quarter_041_018, quarter_041_019, quarter_041_020, quarter_041_021, quarter_041_022, quarter_041_023, quarter_041_024, quarter_041_025, quarter_041_026, quarter_041_027, quarter_041_028, quarter_041_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_041_000_valid
    · exact quarter_041_001_valid
    · exact quarter_041_002_valid
    · exact quarter_041_003_valid
    · exact quarter_041_004_valid
    · exact quarter_041_005_valid
    · exact quarter_041_006_valid
    · exact quarter_041_007_valid
    · exact quarter_041_008_valid
    · exact quarter_041_009_valid
    · exact quarter_041_010_valid
    · exact quarter_041_011_valid
    · exact quarter_041_012_valid
    · exact quarter_041_013_valid
    · exact quarter_041_014_valid
    · exact quarter_041_015_valid
    · exact quarter_041_016_valid
    · exact quarter_041_017_valid
    · exact quarter_041_018_valid
    · exact quarter_041_019_valid
    · exact quarter_041_020_valid
    · exact quarter_041_021_valid
    · exact quarter_041_022_valid
    · exact quarter_041_023_valid
    · exact quarter_041_024_valid
    · exact quarter_041_025_valid
    · exact quarter_041_026_valid
    · exact quarter_041_027_valid
    · exact quarter_041_028_valid
    · exact quarter_041_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
