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

def quarter_029_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 2, 0, 0, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(64079547/100000000), 0, (19192791/25000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (560543/100000000)]
    alternative := .zero
    polynomial := [(-519393814501857258543526403/25500310721794000000000000), (-64079547/560543), (-2265636775767813258543526403/12750155360897000000000000), (-64079547/560543), (-4011879737033769258543526403/25500310721794000000000000)]
    bernstein := [(44871879381266837221547798413/104449272716468224000000000000), (118565569597822284864385637161/261123181791170560000000000000), (900041480821549954429898111503/1958423863433779200000000000000), (728898063109215933426152754593/1632019886194816000000000000000), (1695751689872377268366533628797/4080049715487040000000000000000)]
    reserve := (20781017489/50000000000) }

theorem quarter_029_000_valid : quarter_029_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_029_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_029_000]
  · intro i; fin_cases i <;> norm_num [quarter_029_000]
  · norm_num [quarter_029_000]
  · norm_num [quarter_029_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_029_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_029_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_029_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_029_000]

def quarter_029_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 2, 0, 0, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(60597559/100000000), 0, (19887081/25000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (71153/12500000)]
    alternative := .zero
    polynomial := [(-3567884787796576400012997/202306469885875000000000), (-60597559/569224), (-17703919647340295150012997/101153234942937500000000), (-60597559/569224), (-31839954506884013900012997/202306469885875000000000)]
    bernstein := [(12501935583001258430979791803/32369035181740000000000000000), (26592731454965382940325433177/64738070363480000000000000000), (53950080917615703513363529043/129476140726960000000000000000), (104718388261650603138289401537/258952281453920000000000000000), (193849761346793175966427695083/517904562907840000000000000000)]
    reserve := (74859259883/200000000000) }

theorem quarter_029_001_valid : quarter_029_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_029_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_029_001]
  · intro i; fin_cases i <;> norm_num [quarter_029_001]
  · norm_num [quarter_029_001]
  · norm_num [quarter_029_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_029_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_029_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_029_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_029_001]

def quarter_029_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 2, 0, 0, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(28469751/50000000), 0, (41103203/50000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (577517/100000000)]
    alternative := .zero
    polynomial := [(-198390637679986255814753033/13136247305843000000000000), (-56939502/577517), (-1133327340271023255814753033/6568123652921500000000000), (-56939502/577517), (-2068264042862060255814753033/13136247305843000000000000)]
    bernstein := [(11527812398842346443288633898087/33628793102958080000000000000000), (3089044506232968121565127349497/8407198275739520000000000000000), (2356369666203460441793466878321/6305398706804640000000000000000), (190236389246127754008252617917/525449892233720000000000000000), (43716866270860360664919214927/131362473058430000000000000000)]
    reserve := (41599462591/125000000000) }

theorem quarter_029_002_valid : quarter_029_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_029_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_029_002]
  · intro i; fin_cases i <;> norm_num [quarter_029_002]
  · norm_num [quarter_029_002]
  · norm_num [quarter_029_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_029_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_029_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_029_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_029_002]

def quarter_029_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 2, 0, 0, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(53110117/100000000), 0, (84730841/100000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (585377/100000000)]
    alternative := .zero
    polynomial := [(-340003764663742932710239531/26630062973566000000000000), (-53110117/585377), (-2267298167786181932710239531/13315031486783000000000000), (-53110117/585377), (-4194592570908620932710239531/26630062973566000000000000)]
    bernstein := [(79690490161174118469644132189/266300629735660000000000000000), (345095618111994513874824855393/1065202518942640000000000000000), (1408630571095557185999559254641/4260810075770560000000000000000), (5445712097213912795858473175517/17043240303082240000000000000000), (536280456569952094069498304417/1842512465198080000000000000000)]
    reserve := (291059337019/1000000000000) }

theorem quarter_029_003_valid : quarter_029_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_029_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_029_003]
  · intro i; fin_cases i <;> norm_num [quarter_029_003]
  · norm_num [quarter_029_003]
  · norm_num [quarter_029_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_029_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_029_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_029_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_029_003]

def quarter_029_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 2, 0, 0, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(24557813/50000000), 0, (21776787/25000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (592757/100000000)]
    alternative := .zero
    polynomial := [(-143343884427826251024359563/13482897549803000000000000), (-49115626/592757), (-1134016919364172251024359563/6741448774901500000000000), (-49115626/592757), (-2124689954300518251024359563/13482897549803000000000000)]
    bernstein := [(8820091375988401027759847564517/34516217727495680000000000000000), (967635282974101041790199845167/3451621772749568000000000000000), (297494973461131953373716301943/1035486531824870400000000000000), (9552729943284566272186750359/34516217727495680000000000000), (859512033393321453960086293/3451621772749568000000000000)]
    reserve := (249016865109/1000000000000) }

theorem quarter_029_004_valid : quarter_029_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_029_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_029_004]
  · intro i; fin_cases i <;> norm_num [quarter_029_004]
  · norm_num [quarter_029_004]
  · norm_num [quarter_029_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_029_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_029_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_029_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_029_004]

def quarter_029_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 2, 0, 0, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(44963763/100000000), 0, (44660553/50000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (299807/50000000)]
    alternative := .zero
    polynomial := [(-118578646771640548454882503/13638867413506000000000000), (-44963763/599614), (-1134431113493327548454882503/6819433706753000000000000), (-44963763/599614), (-2150283580215014548454882503/13638867413506000000000000)]
    bernstein := [(738739977257359496538956633/3491550057857536000000000000), (8256344367311587289122568881/34915500578575360000000000000), (255293416136960765965024375403/1047465017357260800000000000000), (815898362708370707000884605233/3491550057857536000000000000000), (7213078694035214263582763440217/34915500578575360000000000000000)]
    reserve := (41317343727/200000000000) }

theorem quarter_029_005_valid : quarter_029_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_029_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_029_005]
  · intro i; fin_cases i <;> norm_num [quarter_029_005]
  · norm_num [quarter_029_005]
  · norm_num [quarter_029_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_029_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_029_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_029_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_029_005]

def quarter_029_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 2, 0, 0, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1270743/3125000), 0, (22839737/25000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (37869/6250000)]
    alternative := .zero
    polynomial := [(-1497850999510546586193607/215342816412750000000000), (-847162/12623), (-17732677941423765336193607/107671408206375000000000), (-847162/12623), (-11322501627778994695397869/71780938804250000000000)]
    bernstein := [(7094624971197313201035914621/42405970001280000000000000000), (13248595199800887356686246297/68909701252080000000000000000), (99284856039911855952429187/496944960952500000000000000), (34129240290295240728989927/179452347010625000000000000), (423635897820925629483109/2588255004960937500000000)]
    reserve := (163676259491/1000000000000) }

theorem quarter_029_006_valid : quarter_029_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_029_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_029_006]
  · intro i; fin_cases i <;> norm_num [quarter_029_006]
  · norm_num [quarter_029_006]
  · norm_num [quarter_029_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_029_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_029_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_029_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_029_006]

def quarter_029_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 2, 0, 0, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7245283/20000000), 0, (93207547/100000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (611587/100000000)]
    alternative := .zero
    polynomial := [(-150687422572205627852459171/27822412434746000000000000), (-36226415/611587), (-2270793650030418627852459171/13911206217373000000000000), (-36226415/611587), (-4390899877488631627852459171/27822412434746000000000000)]
    bernstein := [(533022964331504892934400101/4347251942929062500000000000), (10268426581741151949032370839/69556031086865000000000000000), (43235408984956686979468288849/278224124347460000000000000000), (1301485363751958291458029193347/8903171979118720000000000000000), (8559979570496087711965169757629/71225375832949760000000000000000)]
    reserve := (120181599189/1000000000000) }

theorem quarter_029_007_valid : quarter_029_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_029_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_029_007]
  · intro i; fin_cases i <;> norm_num [quarter_029_007]
  · norm_num [quarter_029_007]
  · norm_num [quarter_029_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_029_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_029_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_029_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_029_007]

def quarter_029_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 2, 0, 0, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7915969/25000000), 0, (4742731/5000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (616623/100000000)]
    alternative := .zero
    polynomial := [(-28580283563198360088284407/7012877735608500000000000), (-31663876/616623), (-189324317857314453362761469/1168812955934750000000000), (-31663876/616623), (-1107365623580688360088284407/7012877735608500000000000)]
    bernstein := [(1389602794071461999576952201193/17952967003157760000000000000000), (919762875047625900038009555597/8976483501578880000000000000000), (495671228434459756387585433713/4488241750789440000000000000000), (227903837404947184315067257877/2244120875394720000000000000000), (85262884701077516071696112633/1122060437697360000000000000000)]
    reserve := (37993891343/500000000000) }

theorem quarter_029_008_valid : quarter_029_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_029_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_029_008]
  · intro i; fin_cases i <;> norm_num [quarter_029_008]
  · norm_num [quarter_029_008]
  · norm_num [quarter_029_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_029_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_029_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_029_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_029_008]

def quarter_029_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 2, 0, 0, 0, 2, 1]
    lambda := ![(3671927/100000000), (7584151/25000000), (7584151/25000000), (7584151/25000000), 0, 0, (265913/5000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2246487/25000000), 0, 0], ![0, 0, 0, 0, 0], ![(179423/12500000), 0, (1024179/20000000), 0, 0]] i.1) i.2
    mu := ![(408251/25000000), (7987079/100000000), (1/100000000), (1/100000000), (7885877/100000000), (1/100000000), (16513/50000000)]
    alternative := .zero
    polynomial := [(-10952232883739295721394124316396809/106152744181619136207232250000000000), (-9162111414075782373/3297265888175000000), (-480839389765743460092572946364874309/53076372090809568103616125000000000), (-9162111414075782373/3297265888175000000), (-950726546647747624463751768413351809/106152744181619136207232250000000000)]
    bernstein := [(1947070354046285904573767213136577438671/16984439069059061793157160000000000000000), (773412785394404969043446450545168739397/6793775627623624717262864000000000000000), (130562654259270340260222083741760107299/1164647250449764237245062400000000000000), (23792163273840061944453835343594486729/217400820083955990952411648000000000000), (1840964459394521995782716953906024279/17392065606716479276192931840000000000)]
    reserve := (3307838221/31250000000) }

theorem quarter_029_009_valid : quarter_029_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_029_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_029_009]
  · intro i; fin_cases i <;> norm_num [quarter_029_009]
  · norm_num [quarter_029_009]
  · norm_num [quarter_029_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_029_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_029_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_029_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_029_009]

def quarter_029_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 2, 0, 0, 0, 2, 1]
    lambda := ![(557663/12500000), (29826473/100000000), (29826473/100000000), (29826473/100000000), 0, 0, (3029639/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8834843/100000000), 0, 0], ![0, 0, 0, 0, 0], ![(1346299/100000000), 0, (295391/5000000), 0, 0]] i.1) i.2
    mu := ![(1901291/100000000), (3945027/50000000), (1/100000000), (1/100000000), (775327/10000000), (1/100000000), (4731/12500000)]
    alternative := .zero
    polynomial := [(-35042866349132852763647635353073/551637167435209341528000000000000), (-112779808024684781/43658298800000000), (-147805490120406384166922688452267/14516767564084456356000000000000), (-112779808024684781/43658298800000000), (-1860521919408769915193138175277691/183879055811736447176000000000000)]
    bernstein := [(9297014296833841045406045022370663/90380233512584698515947520000000000), (57824421147616112598543085305144131/564876459453654365724672000000000000), (1067710927165394121317325880308271849/10591433614756019357337600000000000000), (433377244909184528309359536215499787/4413097339481674732224000000000000000), (521589504975839970794278602623422327/5516371674352093415280000000000000000)]
    reserve := (94553002547/1000000000000) }

theorem quarter_029_010_valid : quarter_029_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_029_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_029_010]
  · intro i; fin_cases i <;> norm_num [quarter_029_010]
  · norm_num [quarter_029_010]
  · norm_num [quarter_029_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_029_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_029_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_029_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_029_010]

def quarter_029_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 2, 0, 0, 0, 2, 1]
    lambda := ![(1050027/20000000), (7338051/25000000), (7338051/25000000), (7338051/25000000), 0, 0, (1673313/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8694361/100000000), 0, 0], ![0, 0, 0, 0, 0], ![(1162419/100000000), 0, (329577/5000000), 0, 0]] i.1) i.2
    mu := ![(2149467/100000000), (3894361/50000000), (1/100000000), (1/100000000), (3814993/50000000), (1/100000000), (42003/100000000)]
    alternative := .zero
    polynomial := [(-694140147879024500575990302026699/30572004549716204012984000000000000), (-2036984054072461379/908749139350000000), (-170227815004575600974609477720586699/15286002274858102006492000000000000), (-2036984054072461379/908749139350000000), (-339761489861272177448642965139146699/30572004549716204012984000000000000)]
    bernstein := [(27886470393380403780362168634782123501/305720045497162040129840000000000000000), (8558652760549884902666412856952085431/94067706306819089270720000000000000000), (438244978399042960553648359005550338809/4891520727954592642077440000000000000000), (131018689621432066908810019086327800579/1505083300909105428331520000000000000000), (6524289719864518020005899679890527546181/78264331647273482273239040000000000000000)]
    reserve := (83362236443/1000000000000) }

theorem quarter_029_011_valid : quarter_029_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_029_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_029_011]
  · intro i; fin_cases i <;> norm_num [quarter_029_011]
  · norm_num [quarter_029_011]
  · norm_num [quarter_029_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_029_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_029_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_029_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_029_011]

def quarter_029_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 2, 0, 0, 0, 2, 1]
    lambda := ![(6037449/100000000), (5782139/20000000), (5782139/20000000), (5782139/20000000), 0, 0, (3615233/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4281791/50000000), 0, 0], ![0, 0, 0, 0, 0], ![(900291/100000000), 0, (3587099/50000000), 0, 0]] i.1) i.2
    mu := ![(1190083/50000000), (7682263/100000000), (1/100000000), (1/100000000), (3757609/50000000), (1/100000000), (45529/100000000)]
    alternative := .zero
    polynomial := [(5426881401139045949208918428837/418545834039079570637000000000000), (-62284869850207445813/34976575212700000000), (-2499897745890604383242923215741163/209272917019539785318500000000000), (-62284869850207445813/34976575212700000000), (-5005222373182347812435055349911163/418545834039079570637000000000000)]
    bernstein := [(85398555307211981539905915001526821397/1071477335140043700830720000000000000000), (42703347383184039277910008396196952599/535738667570021850415360000000000000000), (63060921146604649258080266397313726199/803608001355032775623040000000000000000), (10178714745849160127405785439962430511/133934666892505462603840000000000000000), (4840920076888942521744045000811678437/66967333446252731301920000000000000000)]
    reserve := (9035972891/125000000000) }

theorem quarter_029_012_valid : quarter_029_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_029_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_029_012]
  · intro i; fin_cases i <;> norm_num [quarter_029_012]
  · norm_num [quarter_029_012]
  · norm_num [quarter_029_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_029_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_029_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_029_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_029_012]

def quarter_029_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 2, 0, 0, 0, 2, 1]
    lambda := ![(6822177/100000000), (1424969/5000000), (1424969/5000000), (1424969/5000000), 0, 0, (3839841/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8441747/100000000), 0, 0], ![0, 0, 0, 0, 0], ![(575167/100000000), 0, (7658113/100000000), 0, 0]] i.1) i.2
    mu := ![(2595599/100000000), (946257/12500000), (1/100000000), (1/100000000), (3704149/50000000), (1/100000000), (3029/6250000)]
    alternative := .zero
    polynomial := [(130925091387465205446462196271953/3391650202835028141009600000000000), (-71997393073812861/58794101600000000), (-21414794720693353445562158655495047/1695825101417514070504800000000000), (-71997393073812861/58794101600000000), (-42960514532774172096570779507262047/3391650202835028141009600000000000)]
    bernstein := [(37082743074721973441528347873110500353/542664032453604502561536000000000000000), (24801816764351220314045370064154763851/361776021635736335041024000000000000000), (439302286407844542462524110787785669459/6511968389443254030738432000000000000000), (94141102624910129755149109968115925051/1447104086542945340164096000000000000000), (532575731402719575335191142342078907553/8682624519257672040984576000000000000000)]
    reserve := (1226762093/20000000000) }

theorem quarter_029_013_valid : quarter_029_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_029_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_029_013]
  · intro i; fin_cases i <;> norm_num [quarter_029_013]
  · norm_num [quarter_029_013]
  · norm_num [quarter_029_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_029_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_029_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_029_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_029_013]

def quarter_029_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 2, 0, 0, 0, 2, 1]
    lambda := ![0, (33333333/100000000), (33333333/100000000), (33333333/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (1809931/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9873603/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (8728369/100000000), (1/100000000), (1/100000000), (270777/3125000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(424810512567082735712097/7756936443776000000000000), (-280236097197639/872836900000000), (-2227855480474257068607903/3878468221888000000000000), (-280236097197639/872836900000000), (-4880521473515596872927903/7756936443776000000000000)]
    bernstein := [(1239870554824265802142332502497/19857757296066560000000000000000), (752198612217820036688163297/12411098310041600000000000000), (728763589718627072087685899/12411098310041600000000000000), (440375946349828396328097/7756936443776000000000000), (424810512567082735712097/7756936443776000000000000)]
    reserve := (54765243423/1000000000000) }

theorem quarter_029_014_valid : quarter_029_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_029_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_029_014]
  · intro i; fin_cases i <;> norm_num [quarter_029_014]
  · norm_num [quarter_029_014]
  · norm_num [quarter_029_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_029_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_029_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_029_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_029_014]

def quarter_029_015 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 2, 0, 0, 0, 2, 1]
    lambda := ![0, (33333333/100000000), (33333333/100000000), (33333333/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (10691381/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9873603/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (8716781/100000000), (1/100000000), (1/100000000), (270777/3125000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(220850889553246137611809/4028251833748480000000000), (356379363102873/871678100000000), (-1163072757784647917283551/2014125916874240000000000), (356379363102873/871678100000000), (-2546996405122541972178911/4028251833748480000000000)]
    bernstein := [(220850889553246137611809/4028251833748480000000000), (231144151932222846126049/4028251833748480000000000), (1157736515935973214356103649/19335608801992704000000000000), (401616303208876349838477089/6445202933997568000000000000), (667122781074941062529260233889/10312324694396108800000000000000)]
    reserve := (10965098443/200000000000) }

theorem quarter_029_015_valid : quarter_029_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_029_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_029_015]
  · intro i; fin_cases i <;> norm_num [quarter_029_015]
  · norm_num [quarter_029_015]
  · norm_num [quarter_029_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_029_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_029_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_029_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_029_015]

def quarter_029_016 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 2, 0, 0, 0, 2, 1]
    lambda := ![0, (33333333/100000000), (33333333/100000000), (33333333/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (3076347/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9873603/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2170837/25000000), (1/100000000), (1/100000000), (270777/3125000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(1337340744060483531351777/25080009828224000000000000), (3307899966921/7002700000000), (-7318841649583558333256223/12540004914112000000000000), (3307899966921/7002700000000), (-15975024043227600197864223/25080009828224000000000000)]
    bernstein := [(4158848678207682652969112142177/64204825160253440000000000000000), (2168516330167065057573224960577/32102412580126720000000000000000), (1127883557146089661244867562577/16051206290063360000000000000000), (585306984951849097256431308177/8025603145031680000000000000000), (303117758441113363896591877377/4012801572515840000000000000000)]
    reserve := (8096838259/125000000000) }

theorem quarter_029_016_valid : quarter_029_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_029_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_029_016]
  · intro i; fin_cases i <;> norm_num [quarter_029_016]
  · norm_num [quarter_029_016]
  · norm_num [quarter_029_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_029_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_029_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_029_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_029_016]

def quarter_029_017 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 2, 0, 0, 0, 2, 1]
    lambda := ![0, (33333333/100000000), (33333333/100000000), (33333333/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (55543/400000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9873603/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (8628241/100000000), (1/100000000), (1/100000000), (270777/3125000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(18899957834001669796357/376163697228800000000000), (1851433314819/3451296400000), (-111532725484604817307643/188081848614400000000000), (1851433314819/3451296400000), (-241965408803211304411643/376163697228800000000000)]
    bernstein := [(4552892294830774735226593957/60186191556608000000000000000), (9467539245054140514945719071/120372383113216000000000000000), (58936478158855600369233209239/722234298679296000000000000000), (40686390727398152991866129639/481489532452864000000000000000), (84114037707371718484396458517/962979064905728000000000000000)]
    reserve := (37823395841/500000000000) }

theorem quarter_029_017_valid : quarter_029_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_029_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_029_017]
  · intro i; fin_cases i <;> norm_num [quarter_029_017]
  · norm_num [quarter_029_017]
  · norm_num [quarter_029_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_029_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_029_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_029_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_029_017]

def quarter_029_018 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 2, 0, 0, 0, 2, 1]
    lambda := ![0, (33333333/100000000), (33333333/100000000), (33333333/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (3856709/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9873603/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (534487/6250000), (1/100000000), (1/100000000), (270777/3125000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(281344032458605145192091/6175009553024000000000000), (128556965381097/213794800000000), (-1869819849739355817711909/3087504776512000000000000), (128556965381097/213794800000000), (-4020983731937316780615909/6175009553024000000000000)]
    bernstein := [(1382988672395001243232448892171/15808024455741440000000000000000), (27583019861209692553314274989/304000470302720000000000000000), (92802172049267562880849504919/988001528483840000000000000000), (1844431370689878695955588921/19000029393920000000000000000), (6185681729215285680151512291/61750095530240000000000000000)]
    reserve := (43743248129/500000000000) }

theorem quarter_029_018_valid : quarter_029_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_029_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_029_018]
  · intro i; fin_cases i <;> norm_num [quarter_029_018]
  · norm_num [quarter_029_018]
  · norm_num [quarter_029_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_029_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_029_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_029_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_029_018]

def quarter_029_019 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 2, 0, 0, 0, 2, 1]
    lambda := ![0, (33333333/100000000), (33333333/100000000), (33333333/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (1057711/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9873603/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1056811/12500000), (1/100000000), (1/100000000), (270777/3125000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(479047579038590834592351/12209498118272000000000000), (35257032980763/52840550000000), (-3794450016901632778655649/6104749059136000000000000), (35257032980763/52840550000000), (-8067947612841856391903649/12209498118272000000000000)]
    bernstein := [(12251581033527253836315676551/122094981182720000000000000000), (10143311993889843097626327531/97675984946176000000000000000), (8384534663616973721726111379/78140787956940800000000000000), (106471262183718888019209231/961732774854656000000000000), (17552775044190167883633363/153877243976744960000000000)]
    reserve := (25086168397/250000000000) }

theorem quarter_029_019_valid : quarter_029_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_029_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_029_019]
  · intro i; fin_cases i <;> norm_num [quarter_029_019]
  · norm_num [quarter_029_019]
  · norm_num [quarter_029_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_029_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_029_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_029_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_029_019]

def quarter_029_020 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 2, 0, 0, 0, 2, 1]
    lambda := ![0, (33333333/100000000), (33333333/100000000), (33333333/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (18370517/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9873603/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1667393/20000000), (1/100000000), (1/100000000), (270777/3125000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(46248185029568503295217/1481818828672000000000000), (8388363843057/11420500000000), (-474901339216216202131983/740909414336000000000000), (8388363843057/11420500000000), (-996050863462000907559183/1481818828672000000000000)]
    bernstein := [(2134201451868314591367741/18675476683816960000000000), (358253279191797379982476503/3034764961120256000000000000), (4619541857614182397914616297/37934562014003200000000000000), (1699744049783213481407855277/13548057862144000000000000000), (4372713849875550865785095511/33870144655360000000000000000)]
    reserve := (114278285261/1000000000000) }

theorem quarter_029_020_valid : quarter_029_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_029_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_029_020]
  · intro i; fin_cases i <;> norm_num [quarter_029_020]
  · norm_num [quarter_029_020]
  · norm_num [quarter_029_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_029_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_029_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_029_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_029_020]

def quarter_029_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 2, 0, 0, 0, 2, 1]
    lambda := ![0, (33333333/100000000), (33333333/100000000), (33333333/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (4940969/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9873603/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2049999/25000000), (1/100000000), (1/100000000), (270777/3125000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(101436319681669357494871/4736790009369600000000000), (1168077766097/1453900000000), (-1572633276507981179868329/2368395004684800000000000), (1168077766097/1453900000000), (-3246702872697631717231529/4736790009369600000000000)]
    bernstein := [(98032908678325882668079957351/757886401499136000000000000000), (202215919043560450421982748619/1515772802998272000000000000000), (1249821912686529486565463632333/9094636817989632000000000000000), (857325354090093686630341285459/6063091211993088000000000000000), (1762407155066361193701472631671/12126182423986176000000000000000)]
    reserve := (64675199663/500000000000) }

theorem quarter_029_021_valid : quarter_029_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_029_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_029_021]
  · intro i; fin_cases i <;> norm_num [quarter_029_021]
  · norm_num [quarter_029_021]
  · norm_num [quarter_029_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_029_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_029_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_029_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_029_021]

def quarter_029_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 2, 0, 0, 0, 2, 1]
    lambda := ![0, (33333333/100000000), (33333333/100000000), (33333333/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (5274893/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9873603/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2011119/25000000), (1/100000000), (1/100000000), (270777/3125000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(45349196563992031633783/4646952699417600000000000), (5328174694193/6094300000000), (-1605204421090898293428617/2323476349708800000000000), (5328174694193/6094300000000), (-3255758038745788618491017/4646952699417600000000000)]
    bernstein := [(1732445749747919635624903122583/11896198910509056000000000000000), (74346976331178249565528954723/495674954604544000000000000000), (21512839003361566058568320569/139408580982528000000000000000), (47244793575154686759879827/297881583296000000000000000), (9095925938230271731616779/55852796868000000000000000)]
    reserve := (145630193541/1000000000000) }

theorem quarter_029_022_valid : quarter_029_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_029_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_029_022]
  · intro i; fin_cases i <;> norm_num [quarter_029_022]
  · norm_num [quarter_029_022]
  · norm_num [quarter_029_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_029_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_029_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_029_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_029_022]

def quarter_029_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 2, 0, 0, 0, 2, 1]
    lambda := ![0, (33333333/100000000), (33333333/100000000), (33333333/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (22374263/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9873603/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (7871407/100000000), (1/100000000), (1/100000000), (270777/3125000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-351539038227236775500109/90939561524864000000000000), (745808759208579/787140700000000), (-32818836399567059915372109/45469780762432000000000000), (745808759208579/787140700000000), (-65286133760906883055244109/90939561524864000000000000)]
    bernstein := [(178373744093408921053826583/1093023576020000000000000000), (2935902891708917972665581219/17488377216320000000000000000), (156896104304976514450418026799/909395615248640000000000000000), (5155063760000460926358710429139/29100659687956480000000000000000), (42308335497210173836153826508051/232805277503651840000000000000000)]
    reserve := (163192952107/1000000000000) }

theorem quarter_029_023_valid : quarter_029_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_029_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_029_023]
  · intro i; fin_cases i <;> norm_num [quarter_029_023]
  · norm_num [quarter_029_023]
  · norm_num [quarter_029_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_029_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_029_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_029_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_029_023]

def quarter_029_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 2, 0, 0, 0, 2, 1]
    lambda := ![0, (33333333/100000000), (33333333/100000000), (33333333/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (4717031/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9873603/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (7681887/100000000), (1/100000000), (1/100000000), (270777/3125000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1738650352648571444836189/88750008157824000000000000), (52411455031441/51212580000000), (-33592676758870970863876189/44375004078912000000000000), (52411455031441/51212580000000), (-65446703165093370282916189/88750008157824000000000000)]
    bernstein := [(41377683598646380186429202855171/227200020884029440000000000000000), (327078396565262875158427721783/1747692468338688000000000000000), (1309674936113106624367396558889/6816000626520883200000000000000), (3444993985033524198079042231/17476924683386880000000000000), (4590771716770908322921381379/22720002088402944000000000000)]
    reserve := (182120069521/1000000000000) }

theorem quarter_029_024_valid : quarter_029_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_029_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_029_024]
  · intro i; fin_cases i <;> norm_num [quarter_029_024]
  · norm_num [quarter_029_024]
  · norm_num [quarter_029_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_029_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_029_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_029_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_029_024]

def quarter_029_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 2, 0, 0, 0, 2, 1]
    lambda := ![0, (33333333/100000000), (33333333/100000000), (33333333/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (772813/3125000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9873603/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3738543/50000000), (1/100000000), (1/100000000), (270777/3125000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-324565868615193799479241/8638391107507200000000000), (8586811025243/7788631250000), (-3442120901450736492701641/4319195553753600000000000), (8586811025243/7788631250000), (-6559675934286279185924041/8638391107507200000000000)]
    bernstein := [(447812089681361374011145751/2211428123521843200000000000), (1532478906464409420969857071/7371427078406144000000000000), (141484965223149880082168685101/663428437056552960000000000000), (161144563357774173623168390023/737142707840614400000000000000), (4951973979386289843594111200519/22114281235218432000000000000000)]
    reserve := (25312380997/125000000000) }

theorem quarter_029_025_valid : quarter_029_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_029_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_029_025]
  · intro i; fin_cases i <;> norm_num [quarter_029_025]
  · norm_num [quarter_029_025]
  · norm_num [quarter_029_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_029_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_029_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_029_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_029_025]

def quarter_029_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 2, 0, 0, 0, 2, 1]
    lambda := ![0, (33333333/100000000), (33333333/100000000), (33333333/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (5161433/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9873603/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (907279/12500000), (1/100000000), (1/100000000), (270777/3125000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-607935026077572796343673/10481932193408000000000000), (172047764946189/145164640000000), (-4412489573266026944003673/5240966096704000000000000), (172047764946189/145164640000000), (-8217044120454481091663673/10481932193408000000000000)]
    bernstein := [(6022123309852760320111119098007/26833746415124480000000000000000), (1544347953192846047296538526111/6708436603781120000000000000000), (395752862800068091199062823803/1677109150945280000000000000000), (101345611395785646178113625419/419277287736320000000000000000), (25936083643372049408747901087/104819321934080000000000000000)]
    reserve := (28052937599/125000000000) }

theorem quarter_029_026_valid : quarter_029_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_029_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_029_026]
  · intro i; fin_cases i <;> norm_num [quarter_029_026]
  · norm_num [quarter_029_026]
  · norm_num [quarter_029_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_029_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_029_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_029_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_029_026]

def quarter_029_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 2, 0, 0, 0, 2, 1]
    lambda := ![0, (33333333/100000000), (33333333/100000000), (33333333/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (26815469/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9873603/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1405319/20000000), (1/100000000), (1/100000000), (270777/3125000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1316551873099029153020757/16235864015488000000000000), (893848957728177/702659500000000), (-7244845134492575946255957/8117932007744000000000000), (893848957728177/702659500000000), (-13173138395886122739491157/16235864015488000000000000)]
    bernstein := [(40263830410692127132565083683/162358640154880000000000000000), (165083694140515564695496326393/649434560619520000000000000000), (676398016655881345246982439903/2597738242478080000000000000000), (2769656141859305891713732014213/10390952969912320000000000000000), (11334160612480689253697056639323/41563811879649280000000000000000)]
    reserve := (247993148823/1000000000000) }

theorem quarter_029_027_valid : quarter_029_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_029_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_029_027]
  · intro i; fin_cases i <;> norm_num [quarter_029_027]
  · norm_num [quarter_029_027]
  · norm_num [quarter_029_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_029_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_029_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_029_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_029_027]

def quarter_029_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 2, 0, 0, 0, 2, 1]
    lambda := ![0, (33333333/100000000), (33333333/100000000), (33333333/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (13877157/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9873603/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (6783467/100000000), (1/100000000), (1/100000000), (270777/3125000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-8393981810590607474775969/78370425337984000000000000), (462571895374281/339173350000000), (-37189538371110772323351969/39185212668992000000000000), (462571895374281/339173350000000), (-65985094931630937171927969/78370425337984000000000000)]
    bernstein := [(54834484819889220019157231002191/200628288865239040000000000000000), (28084001816314697118210510549549/100314144432619520000000000000000), (14374581548409025918218067513111/50157072216309760000000000000000), (7353207941169859319923060649829/25078536108154880000000000000000), (3759385042572018843493375121631/12539268054077440000000000000000)]
    reserve := (273313823937/1000000000000) }

theorem quarter_029_028_valid : quarter_029_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_029_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_029_028]
  · intro i; fin_cases i <;> norm_num [quarter_029_028]
  · norm_num [quarter_029_028]
  · norm_num [quarter_029_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_029_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_029_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_029_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_029_028]

def quarter_029_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 2, 0, 0, 0, 2, 1]
    lambda := ![0, (33333333/100000000), (33333333/100000000), (33333333/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (28623581/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9873603/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (6530147/100000000), (1/100000000), (1/100000000), (270777/3125000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-791352488847721368036173/5803367759488000000000000), (954119357125473/653014700000000), (-2937790811621204592324173/2901683879744000000000000), (954119357125473/653014700000000), (-5084229134394687816612173/5803367759488000000000000)]
    bernstein := [(279023570419861849652590111027/928538841518080000000000000000), (114253662594494344577861152463/371415536607232000000000000000), (140271802598845565369771974273/445698643928678400000000000000), (19124525956096234960326270151/59426485857157120000000000000), (7818190784798868847520642083/23770594342862848000000000000)]
    reserve := (300497467573/1000000000000) }

theorem quarter_029_029_valid : quarter_029_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_029_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_029_029]
  · intro i; fin_cases i <;> norm_num [quarter_029_029]
  · norm_num [quarter_029_029]
  · norm_num [quarter_029_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_029_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_029_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_029_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_029_029]

def quarterTable029 : OwnerTable where
  mode := .quarter
  owners := ![0, 2, 0, 0, 0, 2, 1]
  rows := [quarter_029_000, quarter_029_001, quarter_029_002, quarter_029_003, quarter_029_004, quarter_029_005, quarter_029_006, quarter_029_007, quarter_029_008, quarter_029_009, quarter_029_010, quarter_029_011, quarter_029_012, quarter_029_013, quarter_029_014, quarter_029_015, quarter_029_016, quarter_029_017, quarter_029_018, quarter_029_019, quarter_029_020, quarter_029_021, quarter_029_022, quarter_029_023, quarter_029_024, quarter_029_025, quarter_029_026, quarter_029_027, quarter_029_028, quarter_029_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_029_000_valid
    · exact quarter_029_001_valid
    · exact quarter_029_002_valid
    · exact quarter_029_003_valid
    · exact quarter_029_004_valid
    · exact quarter_029_005_valid
    · exact quarter_029_006_valid
    · exact quarter_029_007_valid
    · exact quarter_029_008_valid
    · exact quarter_029_009_valid
    · exact quarter_029_010_valid
    · exact quarter_029_011_valid
    · exact quarter_029_012_valid
    · exact quarter_029_013_valid
    · exact quarter_029_014_valid
    · exact quarter_029_015_valid
    · exact quarter_029_016_valid
    · exact quarter_029_017_valid
    · exact quarter_029_018_valid
    · exact quarter_029_019_valid
    · exact quarter_029_020_valid
    · exact quarter_029_021_valid
    · exact quarter_029_022_valid
    · exact quarter_029_023_valid
    · exact quarter_029_024_valid
    · exact quarter_029_025_valid
    · exact quarter_029_026_valid
    · exact quarter_029_027_valid
    · exact quarter_029_028_valid
    · exact quarter_029_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
