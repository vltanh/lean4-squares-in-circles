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

def quarter_005_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(64079547/100000000), 0, (19192791/25000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (560543/100000000)]
    alternative := .zero
    polynomial := [(-519393814501857258543526403/25500310721794000000000000), (-64079547/560543), (-2265636775767813258543526403/12750155360897000000000000), (-64079547/560543), (-4011879737033769258543526403/25500310721794000000000000)]
    bernstein := [(44871879381266837221547798413/104449272716468224000000000000), (118565569597822284864385637161/261123181791170560000000000000), (900041480821549954429898111503/1958423863433779200000000000000), (728898063109215933426152754593/1632019886194816000000000000000), (1695751689872377268366533628797/4080049715487040000000000000000)]
    reserve := (20781017489/50000000000) }

theorem quarter_005_000_valid : quarter_005_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_000]
  · intro i; fin_cases i <;> norm_num [quarter_005_000]
  · norm_num [quarter_005_000]
  · norm_num [quarter_005_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_000]

def quarter_005_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(60597559/100000000), 0, (19887081/25000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (71153/12500000)]
    alternative := .zero
    polynomial := [(-3567884787796576400012997/202306469885875000000000), (-60597559/569224), (-17703919647340295150012997/101153234942937500000000), (-60597559/569224), (-31839954506884013900012997/202306469885875000000000)]
    bernstein := [(12501935583001258430979791803/32369035181740000000000000000), (26592731454965382940325433177/64738070363480000000000000000), (53950080917615703513363529043/129476140726960000000000000000), (104718388261650603138289401537/258952281453920000000000000000), (193849761346793175966427695083/517904562907840000000000000000)]
    reserve := (74859259883/200000000000) }

theorem quarter_005_001_valid : quarter_005_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_001]
  · intro i; fin_cases i <;> norm_num [quarter_005_001]
  · norm_num [quarter_005_001]
  · norm_num [quarter_005_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_001]

def quarter_005_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(28469751/50000000), 0, (41103203/50000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (577517/100000000)]
    alternative := .zero
    polynomial := [(-198390637679986255814753033/13136247305843000000000000), (-56939502/577517), (-1133327340271023255814753033/6568123652921500000000000), (-56939502/577517), (-2068264042862060255814753033/13136247305843000000000000)]
    bernstein := [(11527812398842346443288633898087/33628793102958080000000000000000), (3089044506232968121565127349497/8407198275739520000000000000000), (2356369666203460441793466878321/6305398706804640000000000000000), (190236389246127754008252617917/525449892233720000000000000000), (43716866270860360664919214927/131362473058430000000000000000)]
    reserve := (41599462591/125000000000) }

theorem quarter_005_002_valid : quarter_005_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_002]
  · intro i; fin_cases i <;> norm_num [quarter_005_002]
  · norm_num [quarter_005_002]
  · norm_num [quarter_005_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_002]

def quarter_005_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(53110117/100000000), 0, (84730841/100000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (585377/100000000)]
    alternative := .zero
    polynomial := [(-340003764663742932710239531/26630062973566000000000000), (-53110117/585377), (-2267298167786181932710239531/13315031486783000000000000), (-53110117/585377), (-4194592570908620932710239531/26630062973566000000000000)]
    bernstein := [(79690490161174118469644132189/266300629735660000000000000000), (345095618111994513874824855393/1065202518942640000000000000000), (1408630571095557185999559254641/4260810075770560000000000000000), (5445712097213912795858473175517/17043240303082240000000000000000), (536280456569952094069498304417/1842512465198080000000000000000)]
    reserve := (291059337019/1000000000000) }

theorem quarter_005_003_valid : quarter_005_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_003]
  · intro i; fin_cases i <;> norm_num [quarter_005_003]
  · norm_num [quarter_005_003]
  · norm_num [quarter_005_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_003]

def quarter_005_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(24557813/50000000), 0, (21776787/25000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (592757/100000000)]
    alternative := .zero
    polynomial := [(-143343884427826251024359563/13482897549803000000000000), (-49115626/592757), (-1134016919364172251024359563/6741448774901500000000000), (-49115626/592757), (-2124689954300518251024359563/13482897549803000000000000)]
    bernstein := [(8820091375988401027759847564517/34516217727495680000000000000000), (967635282974101041790199845167/3451621772749568000000000000000), (297494973461131953373716301943/1035486531824870400000000000000), (9552729943284566272186750359/34516217727495680000000000000), (859512033393321453960086293/3451621772749568000000000000)]
    reserve := (249016865109/1000000000000) }

theorem quarter_005_004_valid : quarter_005_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_004]
  · intro i; fin_cases i <;> norm_num [quarter_005_004]
  · norm_num [quarter_005_004]
  · norm_num [quarter_005_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_004]

def quarter_005_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(44963763/100000000), 0, (44660553/50000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (299807/50000000)]
    alternative := .zero
    polynomial := [(-118578646771640548454882503/13638867413506000000000000), (-44963763/599614), (-1134431113493327548454882503/6819433706753000000000000), (-44963763/599614), (-2150283580215014548454882503/13638867413506000000000000)]
    bernstein := [(738739977257359496538956633/3491550057857536000000000000), (8256344367311587289122568881/34915500578575360000000000000), (255293416136960765965024375403/1047465017357260800000000000000), (815898362708370707000884605233/3491550057857536000000000000000), (7213078694035214263582763440217/34915500578575360000000000000000)]
    reserve := (41317343727/200000000000) }

theorem quarter_005_005_valid : quarter_005_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_005]
  · intro i; fin_cases i <;> norm_num [quarter_005_005]
  · norm_num [quarter_005_005]
  · norm_num [quarter_005_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_005]

def quarter_005_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1270743/3125000), 0, (22839737/25000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (37869/6250000)]
    alternative := .zero
    polynomial := [(-1497850999510546586193607/215342816412750000000000), (-847162/12623), (-17732677941423765336193607/107671408206375000000000), (-847162/12623), (-11322501627778994695397869/71780938804250000000000)]
    bernstein := [(7094624971197313201035914621/42405970001280000000000000000), (13248595199800887356686246297/68909701252080000000000000000), (99284856039911855952429187/496944960952500000000000000), (34129240290295240728989927/179452347010625000000000000), (423635897820925629483109/2588255004960937500000000)]
    reserve := (163676259491/1000000000000) }

theorem quarter_005_006_valid : quarter_005_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_006]
  · intro i; fin_cases i <;> norm_num [quarter_005_006]
  · norm_num [quarter_005_006]
  · norm_num [quarter_005_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_006]

def quarter_005_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7245283/20000000), 0, (93207547/100000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (611587/100000000)]
    alternative := .zero
    polynomial := [(-150687422572205627852459171/27822412434746000000000000), (-36226415/611587), (-2270793650030418627852459171/13911206217373000000000000), (-36226415/611587), (-4390899877488631627852459171/27822412434746000000000000)]
    bernstein := [(533022964331504892934400101/4347251942929062500000000000), (10268426581741151949032370839/69556031086865000000000000000), (43235408984956686979468288849/278224124347460000000000000000), (1301485363751958291458029193347/8903171979118720000000000000000), (8559979570496087711965169757629/71225375832949760000000000000000)]
    reserve := (120181599189/1000000000000) }

theorem quarter_005_007_valid : quarter_005_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_007]
  · intro i; fin_cases i <;> norm_num [quarter_005_007]
  · norm_num [quarter_005_007]
  · norm_num [quarter_005_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_007]

def quarter_005_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![(1/10000000), (1/10000000), (1/50000000), (1/100000000), 0, 0, (49999989/50000000)]
    cone := fun i => (![![0, 0, (24549207/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(31663869/100000000), 0, (94854599/100000000), 0, 0]] i.1) i.2
    mu := ![(5686519/25000000), (1/100000000), (3/100000000), (1/100000000), (1/100000000), (1/100000000), (616623/100000000)]
    alternative := .zero
    polynomial := [(-28580266605832163949535189/7012876810674000000000000), (-1583193105808261/30831150000000), (-567972628091655365823115189/3506438405337000000000000), (-1583193105808261/30831150000000), (-1107364989577478567696695189/7012876810674000000000000)]
    bernstein := [(1389603926487125936233268576011/17952964635325440000000000000000), (919763303978788916295487971319/8976482317662720000000000000000), (1487014254710148096459940658153/13464723476494080000000000000000), (75967980554637004152524860293/748040193138560000000000000000), (85262952244848471407862488891/1122060289707840000000000000000)]
    reserve := (9498481613/125000000000) }

theorem quarter_005_008_valid : quarter_005_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_008]
  · intro i; fin_cases i <;> norm_num [quarter_005_008]
  · norm_num [quarter_005_008]
  · norm_num [quarter_005_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_008]

def quarter_005_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![(12711067/50000000), (12711067/50000000), (5383483/100000000), (5383483/100000000), 0, 0, (19194383/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1594631/100000000), 0, 0], ![0, 0, 0, 0, 0], ![(10361023/100000000), 0, (18482063/50000000), 0, 0]] i.1) i.2
    mu := ![(2908553/25000000), (1/100000000), (6945601/100000000), (1/100000000), (279883/20000000), (1/100000000), (238387/100000000)]
    alternative := .zero
    polynomial := [(-5939442865547275171671985685676594421/5391453860881989936334052000000000000), (-35176882025472155679/2069676231983750000), (-167774179674837068607317082629159954421/2695726930440994968167026000000000000), (-35176882025472155679/2069676231983750000), (-329608916484126862042962179572643314421/5391453860881989936334052000000000000)]
    bernstein := [(63736719392998250431526534887370200340699/862632617741118389813448320000000000000000), (28412284596970094074543474666384448695193/345053047096447355925379328000000000000000), (11628459597715893831498384344998096191539/138021218838578942370151731200000000000000), (879930034119611645017124488607780325901/11041697507086315389612138496000000000000), (4669158539221074926016395137398448527/67948907735915787012997775360000000000)]
    reserve := (34357863097/500000000000) }

theorem quarter_005_009_valid : quarter_005_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_009]
  · intro i; fin_cases i <;> norm_num [quarter_005_009]
  · norm_num [quarter_005_009]
  · norm_num [quarter_005_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_009]

def quarter_005_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![(24833417/100000000), (24833417/100000000), (7287489/100000000), (7287489/100000000), 0, 0, (8939547/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2158613/100000000), 0, 0], ![0, 0, 0, 0, 0], ![(3972519/50000000), 0, (34864371/100000000), 0, 0]] i.1) i.2
    mu := ![(1100057/10000000), (1/100000000), (6960867/100000000), (1/100000000), (1894353/100000000), (1/100000000), (44671/20000000)]
    alternative := .zero
    polynomial := [(-194933337414112155467676146354470141/287993437355764195602932000000000000), (-671460466372439050141/51824814959500000000), (-8303827370323507658592509675799326141/143996718677882097801466000000000000), (-671460466372439050141/51824814959500000000), (-16412721403232903161717343205244182141/287993437355764195602932000000000000)]
    bernstein := [(2501970363223430677384019114350011771/47184844776368405807584378880000000000), (18030194218893334548107410436105203127/294905279852302536297402368000000000000), (349438444457411896300499611637402646133/5529473997230672555576294400000000000000), (136521744482915355675833661722635796479/2303947498846113564823456000000000000000), (142145780915492759642400336137420139659/2879934373557641956029320000000000000000)]
    reserve := (49357298631/1000000000000) }

theorem quarter_005_010_valid : quarter_005_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_010]
  · intro i; fin_cases i <;> norm_num [quarter_005_010]
  · norm_num [quarter_005_010]
  · norm_num [quarter_005_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_010]

def quarter_005_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![(3036943/12500000), (3036943/12500000), (9092109/100000000), (9092109/100000000), 0, 0, (16612347/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (673289/25000000), 0, 0], ![0, 0, 0, 0, 0], ![(180317/3125000), 0, (16359903/50000000), 0, 0]] i.1) i.2
    mu := ![(5200167/50000000), (1/100000000), (6967851/100000000), (1/100000000), (2363457/100000000), (1/100000000), (208497/100000000)]
    alternative := .zero
    polynomial := [(-6481512860036019184270864727152411/17402686675768470560830500000000000), (-3778752801633110491/403548897207500000), (-464398543396287705972599673460402411/8701343337884235280415250000000000), (-3778752801633110491/403548897207500000), (-922315573932539392760928482193652411/17402686675768470560830500000000000)]
    bernstein := [(5967748757943852123413960720395755389/174026866757684705608305000000000000000), (29272162801812226332685259674871415067/696107467030738822433220000000000000000), (369317496022715024322955198555487504603/8353289604368865869198640000000000000000), (454657017315886828107862438793945592503/11137719472491821158931520000000000000000), (1421360083983679729571924270791104557909/44550877889967284635726080000000000000000)]
    reserve := (31904199227/1000000000000) }

theorem quarter_005_011_valid : quarter_005_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_011]
  · intro i; fin_cases i <;> norm_num [quarter_005_011]
  · norm_num [quarter_005_011]
  · norm_num [quarter_005_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_011]

def quarter_005_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![(11097379/50000000), (11097379/50000000), (2540049/25000000), (2540049/25000000), (3189141/100000000), (85189/2500000), (28693391/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1786359/50000000), 0, (25062537/100000000), 0, 0]] i.1) i.2
    mu := ![(4583057/50000000), (1/100000000), (325337/5000000), (1/100000000), (1345389/50000000), (117929/10000000), (90339/50000000)]
    alternative := .zero
    polynomial := [(-69449074484584170317961816534877879289/445236998324761884400844129812500000000), (-28269582147532816189/4898436540500000000), (-40934280396396279484569517470783337032781/890473996649523768801688259625000000000), (-28269582147532816189/4898436540500000000), (-13598460749142370381311197945904527091401/296824665549841256267229419875000000000)]
    bernstein := [(43911138565942087909194269975802514747573157/2279613431422780848132321944640000000000000000), (29821242614331235085276373182289943454511769/1139806715711390424066160972320000000000000000), (48299406419808033458304554053751267115969619/1709710073567085636099241458480000000000000000), (2427179340425561421364172437151113218830047/94983892975949202005513414360000000000000000), (2576998268053124652899806464073503211698397/142475839463923803008270121540000000000000000)]
    reserve := (723490601/40000000000) }

theorem quarter_005_012_valid : quarter_005_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_012]
  · intro i; fin_cases i <;> norm_num [quarter_005_012]
  · norm_num [quarter_005_012]
  · norm_num [quarter_005_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_012]

def quarter_005_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![(171157/800000), (171157/800000), (11569141/100000000), (11569141/100000000), (1915987/50000000), (65347/1562500), (5211657/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1951627/100000000), 0, (21802891/100000000), 0, 0]] i.1) i.2
    mu := ![(4259671/50000000), (1/100000000), (3198561/50000000), (1/100000000), (123179/4000000), (57331/4000000), (41111/25000000)]
    alternative := .zero
    polynomial := [(-10590203738848377489431743528829448553/226035617354738152554260194800000000000), (-32964255186618562829/10519683301680000000), (-4712656883104246343689599212572595276053/113017808677369076277130097400000000000), (-32964255186618562829/10519683301680000000), (-9414723562469644309889766681616361103553/226035617354738152554260194800000000000)]
    bernstein := [(29513755605521812616402403814070127267721/5166528396679729201240233024000000000000000), (41925941524726246464980407748133765823707/3444352264453152800826822016000000000000000), (6194123881099546672529976778226241185303741/433988385321097252904179574016000000000000000), (1160518011165397223707870343000088396934749/96441863404688278423151016448000000000000000), (1052906190802761651956316339693537354148949/192883726809376556846302032896000000000000000)]
    reserve := (5458761131/1000000000000) }

theorem quarter_005_013_valid : quarter_005_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_013]
  · intro i; fin_cases i <;> norm_num [quarter_005_013]
  · norm_num [quarter_005_013]
  · norm_num [quarter_005_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_013]

def quarter_005_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), (-1/80)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![(10417489/50000000), (10417489/50000000), (12522229/100000000), (12522229/100000000), (4297149/100000000), (4758139/100000000), (24230299/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(908317/100000000), 0, (1945513/10000000), 0, 0]] i.1) i.2
    mu := ![(1009339/12500000), (1/100000000), (39227/625000), (1/100000000), (836309/25000000), (81001/5000000), (2391/3125000)]
    alternative := .zero
    polynomial := [(-535780220678760133703227345224041161/25651860428006849285798028000000000000), (-4318209483882189283/1500668112000000000), (-82447824581036628627786831883430010253/1068827517833618720241584500000000000), (-4318209483882189283/1500668112000000000), (-1978212009724200326933180737857096204911/25651860428006849285798028000000000000)]
    bernstein := [(187467598511435879469097743405920781249889/65668762695697534171642951680000000000000000), (776675453931806556230090936931670387064789/131337525391395068343285903360000000000000000), (1828663409567168615841921954030814819100489/262675050782790136686571806720000000000000000), (3152855871715521990198796566630254837196989/525350101565580273373143613440000000000000000), (3187079881737240668914658542883345829034289/1050700203131160546746287226880000000000000000)]
    reserve := (713686351/250000000000) }

theorem quarter_005_014_valid : quarter_005_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_014]
  · intro i; fin_cases i <;> norm_num [quarter_005_014]
  · norm_num [quarter_005_014]
  · norm_num [quarter_005_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_014]

def quarter_005_015 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/80), (-1/160)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![(4113683/20000000), (4113683/20000000), (6483509/50000000), (6483509/50000000), (282673/6250000), (5041953/100000000), (5841103/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(109511/25000000), 0, (1144897/6250000), 0, 0]] i.1) i.2
    mu := ![(1966359/25000000), (1/100000000), (3106363/50000000), (1/100000000), (3470089/100000000), (855731/50000000), (1153/3125000)]
    alternative := .zero
    polynomial := [(-1629880341603880161923811590698519070927/167306258852329701468848228472000000000000), (-1974188338715930609/716327307800000000), (-12410787494748912965094654862118364286595927/83653129426164850734424114236000000000000), (-1974188338715930609/716327307800000000), (-24819945109156222050027385912646030054120927/167306258852329701468848228472000000000000)]
    bernstein := [(10474103584580347638592556290066366503000893473/6852864362591424572164023438213120000000000000000), (13784799255289247807890305050454303201746746891/4568576241727616381442682292142080000000000000000), (41587908803883685714286337765343426841085010117/11747767478728156409424040179793920000000000000000), (1316173463644452371135231804046820272885157537/424983836439778268041179748106240000000000000000), (185098372672961518129462663733725215806341296673/109645829801462793154624375011409920000000000000000)]
    reserve := (1528427097/1000000000000) }

theorem quarter_005_015_valid : quarter_005_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_015]
  · intro i; fin_cases i <;> norm_num [quarter_005_015]
  · norm_num [quarter_005_015]
  · norm_num [quarter_005_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_015]

def quarter_005_016 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/160), (-1/320)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![(255481/1250000), (255481/1250000), (13181747/100000000), (13181747/100000000), (926729/20000000), (5182479/100000000), (11471711/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(21509/10000000), 0, (8879967/50000000), 0, 0]] i.1) i.2
    mu := ![(7764031/100000000), (1/100000000), (6180209/100000000), (1/100000000), (3530557/100000000), (439151/25000000), (18117/100000000)]
    alternative := .zero
    polynomial := [(-112729161774123033696008803349049946439/24505926196829388073761798538200000000000), (-1509729619850970359/559834232265000000), (-3565138827777333832069818305174601374884439/12252963098414694036880899269100000000000), (-1509729619850970359/559834232265000000), (-7130164926392893541105940601545853699822439/24505926196829388073761798538200000000000)]
    bernstein := [(14279268365073748814808907547977547838741060761/16060203792354107768020532289994752000000000000000), (1580394287765183072614861146541405671811914617/973345684385097440486092866060288000000000000000), (363211833778649692924729232402607745151185153483/192722445508249293216246387479937024000000000000000), (167701922903515291218755285872134859619331481/100297915955373038363906524839936000000000000000), (28148397728883790195864450492917573147694758929/28551473408629524920925390737768448000000000000000)]
    reserve := (88910879/100000000000) }

theorem quarter_005_016_valid : quarter_005_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_016]
  · intro i; fin_cases i <;> norm_num [quarter_005_016]
  · norm_num [quarter_005_016]
  · norm_num [quarter_005_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_016]

def quarter_005_017 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/320), (-1/640)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![(1273397/6250000), (1273397/6250000), (1328723/10000000), (1328723/10000000), (234429/5000000), (5252357/100000000), (22735897/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(53287/50000000), 0, (1748329/10000000), 0, 0]] i.1) i.2
    mu := ![(7714131/100000000), (1/100000000), (308189/5000000), (1/100000000), (890077/25000000), (1779019/100000000), (8977/100000000)]
    alternative := .zero
    polynomial := [(-783645276885188953308030293951974979/367329414352826373628094895750000000000), (-368991419262628679/138330632650000000), (-105833787080883847980881910047533596466229/183664707176413186814047447875000000000), (-368991419262628679/138330632650000000), (-211666790516490810772810512064773240957479/367329414352826373628094895750000000000)]
    bernstein := [(2215508183383038545972820722949423975906703321/3851728079844292675534532334059520000000000000000), (2413850707025901433098955484443753467251137907/2567818719896195117023021556039680000000000000000), (49474982776398464967588923585290007470701402763/46220736958131512106414388008714240000000000000000), (9925179615599960432215429394842359735929608307/10271274879584780468092086224158720000000000000000), (38685773836778734983582738922794058365060405721/61627649277508682808552517344952320000000000000000)]
    reserve := (143799623/250000000000) }

theorem quarter_005_017_valid : quarter_005_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_017]
  · intro i; fin_cases i <;> norm_num [quarter_005_017]
  · norm_num [quarter_005_017]
  · norm_num [quarter_005_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_017]

def quarter_005_018 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/640), (-1/1280)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![(10171249/50000000), (10171249/50000000), (6669753/50000000), (6669753/50000000), (58949/1250000), (1321799/25000000), (181063/800000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(26523/50000000), 0, (17345617/100000000), 0, 0]] i.1) i.2
    mu := ![(3844691/50000000), (1/100000000), (1538881/25000000), (1/100000000), (446883/12500000), (1790187/100000000), (1117/25000000)]
    alternative := .zero
    polynomial := [(-22349612798041991135096241078535381/24141695609844959741463813000000000000), (-912092954136068711/343786015400000000), (-13843874753639864049545527725076060244131/12070847804922479870731906500000000000), (-912092954136068711/343786015400000000), (-27687727157666930057099920353911041952881/24141695609844959741463813000000000000)]
    bernstein := [(1699773328713034900906318177283029151641771919/4050304418526206160938425468846080000000000000000), (1624139480346002670352724856227873601819984773/2700202945684137440625616979230720000000000000000), (4628752667651542993996906220632499185739924651/6943379003187781990180157946593280000000000000000), (6643906708036009499610837910746896993922807173/10800811782736549762502467916922880000000000000000), (28964600770458360599263799763932618890119826319/64804870696419298575014807501537280000000000000000)]
    reserve := (209832787/500000000000) }

theorem quarter_005_018_valid : quarter_005_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_018]
  · intro i; fin_cases i <;> norm_num [quarter_005_018]
  · norm_num [quarter_005_018]
  · norm_num [quarter_005_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_018]

def quarter_005_019 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/1280), 0⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![(1016067/5000000), (1016067/5000000), (6687093/50000000), (6687093/50000000), (4734099/100000000), (5310383/100000000), (22564467/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(4407/25000000), 0, (17254077/100000000), 0, 0]] i.1) i.2
    mu := ![(1918239/25000000), (1/100000000), (3075737/50000000), (1/100000000), (3584857/100000000), (1797617/100000000), (891/20000000)]
    alternative := .zero
    polynomial := [(1156994003379482953052782593494097791/11292168908841531337515626199000000000000), (-259024356188767/302081312500000), (-6455115569847978995208791590543503621482209/5646084454420765668757813099500000000000), (-259024356188767/302081312500000), (-12910232296689961369900536233869600737062209/11292168908841531337515626199000000000000)]
    bernstein := [(2259641902076365244572606420981872422003365286591/30312185102738988963242970258541117440000000000000000), (37886773043812650222606388275545191820320853/148008716321967719547084815715532800000000000000), (17822424023654014950772736781604312198600991/55503268620737894830156805893324800000000000000), (24385088312917340947938285624747725653/90337351270732250700125009592000000000000), (1156994003379482953052782593494097791/11292168908841531337515626199000000000000)]
    reserve := (74545661/1000000000000) }

theorem quarter_005_019_valid : quarter_005_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_019]
  · intro i; fin_cases i <;> norm_num [quarter_005_019]
  · norm_num [quarter_005_019]
  · norm_num [quarter_005_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_019]

def quarter_005_020 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/2560)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![(634659/3125000), (634659/3125000), (13397999/100000000), (13397999/100000000), (2372691/50000000), (1064879/20000000), (22516049/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (343879/2000000), 0, 0]] i.1) i.2
    mu := ![(1915449/25000000), (1/100000000), (614779/10000000), (1/100000000), (89787/2500000), (1802157/100000000), (4483/100000000)]
    alternative := .zero
    polynomial := [(18605497684735461357339374663469647/189824352192496461527727486000000000000), (137237255619583/153694750000000), (-107383539243571676083454210356698594260353/94912176096248230763863743000000000000), (137237255619583/153694750000000), (-214767097092641036902369778052771851990353/189824352192496461527727486000000000000)]
    bernstein := [(18605497684735461357339374663469647/189824352192496461527727486000000000000), (102277962807367995077276743562583089/552216297287262433535207232000000000000), (909288259551013081122702099646480467397247/3732098623586234430804344556748800000000000000), (10879548220573810337317799431108465070308379/39809051984919833928579675271987200000000000000), (2235309519810815371428177930792748680411719568047/8152893846511581988573117495702978560000000000000000)]
    reserve := (49007141/500000000000) }

theorem quarter_005_020_valid : quarter_005_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_020]
  · intro i; fin_cases i <;> norm_num [quarter_005_020]
  · norm_num [quarter_005_020]
  · norm_num [quarter_005_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_020]

def quarter_005_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/2560), (1/1280)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![(203057/1000000), (203057/1000000), (2682207/20000000), (2682207/20000000), (4749793/100000000), (2664623/50000000), (22487491/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2145639/12500000), 0, 0]] i.1) i.2
    mu := ![(1531173/20000000), (1/100000000), (6146681/100000000), (1/100000000), (3594957/100000000), (1803813/100000000), (1131/12500000)]
    alternative := .zero
    polynomial := [(-349276513893250702100043744641149433/5113037596253142962027519898000000000000), (274383660367121/307334050000000), (-476765937197847350504906114188641671242311/852172932708857160337919983000000000000), (274383660367121/307334050000000), (-2860595273910570209778734585088105386304433/5113037596253142962027519898000000000000)]
    bernstein := [(14278993009701987731045108923185865186715962465989/73201097530419003863735892712997519360000000000000000), (140667795791432721544718482013931084435480118141/587174579121008052382908230318161920000000000000000), (705452404277133102470116184403666682215673167827/2614324911800678709419139025464197120000000000000000), (41966389097503338721836678303328572246273794941/146793644780252013095727057579540480000000000000000), (1316268775376396033202613303587893544838085320389/4575068595651187741483493294562344960000000000000000)]
    reserve := (39013057/200000000000) }

theorem quarter_005_021_valid : quarter_005_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_021]
  · intro i; fin_cases i <;> norm_num [quarter_005_021]
  · norm_num [quarter_005_021]
  · norm_num [quarter_005_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_021]

def quarter_005_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/1280), (1/640)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![(2030063/10000000), (2030063/10000000), (13430557/100000000), (13430557/100000000), (4756391/100000000), (2668249/50000000), (22444737/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3424383/20000000), 0, 0]] i.1) i.2
    mu := ![(7646991/100000000), (1/100000000), (3073059/50000000), (1/100000000), (900041/25000000), (1806291/100000000), (9031/50000000)]
    alternative := .zero
    polynomial := [(-42372444353858047637243816320814711/105608335272870908855269827000000000000), (274272386256421/307305900000000), (-1341639619042320416551809920899487305201/4800378876039586766148628500000000000), (274272386256421/307305900000000), (-29516029246486695306092181015972399899711/105608335272870908855269827000000000000)]
    bernstein := [(3951958460915026162202221554547869825729481721/31498912929304429830776437793095680000000000000000), (10134242331992789600157279755176491487805955563/47248369393956644746164656689643520000000000000000), (5317053910463549865943609981849661412791677097/19328878388436809214340086827581440000000000000000), (3629234869944926051677367752948154644943901163/11812092348489161186541164172410880000000000000000), (5509997731092686325953064995086037055770289089/17718138522733741779811746258616320000000000000000)]
    reserve := (3920729/31250000000) }

theorem quarter_005_022_valid : quarter_005_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_022]
  · intro i; fin_cases i <;> norm_num [quarter_005_022]
  · norm_num [quarter_005_022]
  · norm_num [quarter_005_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_022]

def quarter_005_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/640), (3/1280)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![(10146947/50000000), (10146947/50000000), (3364131/25000000), (3364131/25000000), (4765153/100000000), (1336531/25000000), (22387887/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (17064431/100000000), 0, 0]] i.1) i.2
    mu := ![(1193/15625), (1/100000000), (1535971/25000000), (1/100000000), (225443/6250000), (90479/5000000), (13571/50000000)]
    alternative := .zero
    polynomial := [(-23896743326164971365557804876998929/32463835661752743256784704000000000000), (34261402070667/38399275000000), (-3007112601686652859430295727926600358929/16231917830876371628392352000000000000), (34261402070667/38399275000000), (-6014201306629979553889225898048323718929/32463835661752743256784704000000000000)]
    bernstein := [(1120525549181255160198074182644388493189804271/5446527830857287122116204445040640000000000000000), (2907632644359874696196242234643944187672171213/10893055661714574244232408890081280000000000000000), (6737860528275607133534354948810779769342376039/21786111323429148488464817780162560000000000000000), (14499774451073574410087322285778908365554116917/43572222646858296976929635560325120000000000000000), (29405372748388625161005070211842652526364801951/87144445293716593953859271120650240000000000000000)]
    reserve := (205732089/1000000000000) }

theorem quarter_005_023_valid : quarter_005_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_023]
  · intro i; fin_cases i <;> norm_num [quarter_005_023]
  · norm_num [quarter_005_023]
  · norm_num [quarter_005_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_023]

def quarter_005_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/1280), (1/320)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![(4057437/20000000), (4057437/20000000), (13482421/100000000), (13482421/100000000), (4773877/100000000), (5355699/100000000), (5582803/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (531471/3125000), 0, 0]] i.1) i.2
    mu := ![(238233/3125000), (1/100000000), (6141639/100000000), (1/100000000), (451749/12500000), (453213/25000000), (18091/50000000)]
    alternative := .zero
    polynomial := [(-1720476681399676436091897140731122983/1605737538039266908028791416000000000000), (182606951382607/204721300000000), (-111140273705845557476747173194076471602983/802868769019633454014395708000000000000), (182606951382607/204721300000000), (-222278826935009715277058254491012212082983/1605737538039266908028791416000000000000)]
    bernstein := [(1115147467714601385226293317385192318395890948777/4310368882398879583624186848828456960000000000000000), (329951488564801844004674869410151617845474066659/1077592220599719895906046712207114240000000000000000), (274456459149593882907119942035481270082294597859/808194165449789921929535034155335680000000000000000), (24172386606633730076824864126238941095626816651/67349513787482493494127919512944640000000000000000), (6131251584197780587805142137893544351431718617/16837378446870623373531979878236160000000000000000)]
    reserve := (4042387/15625000000) }

theorem quarter_005_024_valid : quarter_005_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_024]
  · intro i; fin_cases i <;> norm_num [quarter_005_024]
  · norm_num [quarter_005_024]
  · norm_num [quarter_005_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_024]

def quarter_005_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/320), (3/640)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![(5069293/25000000), (5069293/25000000), (2704227/20000000), (2704227/20000000), (4786889/100000000), (5369967/100000000), (2224653/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2115159/12500000), 0, 0]] i.1) i.2
    mu := ![(7605927/100000000), (1/100000000), (1535119/25000000), (1/100000000), (3624311/100000000), (1817731/100000000), (13487/25000000)]
    alternative := .zero
    polynomial := [(-1524448539746127571145404436556380149/879189759571162979867619708450000000000), (27368947356339/30702380000000), (-20294197785254921917247662129206150591137/219797439892790744966904927112500000000), (27368947356339/30702380000000), (-81175266692479941541419503112388045984399/879189759571162979867619708450000000000)]
    bernstein := [(1384059501070826175054256466039379849037260401/9218972813320917927776692034076672000000000000000), (5032322920216941548358185911745702068317078803/18437945626641835855553384068153344000000000000000), (39623041989839951107165257456851462851421810027/110627673759851015133320304408920064000000000000000), (29930666469094329233857302543390819458168573227/73751782506567343422213536272613376000000000000000), (61350296088577243280188664992044129067478476481/147503565013134686844427072545226752000000000000000)]
    reserve := (150131639/1000000000000) }

theorem quarter_005_025_valid : quarter_005_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_025]
  · intro i; fin_cases i <;> norm_num [quarter_005_025]
  · norm_num [quarter_005_025]
  · norm_num [quarter_005_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_025]

def quarter_005_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/640), (1/160)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![(5065979/25000000), (5065979/25000000), (1357251/10000000), (1357251/10000000), (4804103/100000000), (1077763/20000000), (2213423/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (16807313/100000000), 0, 0]] i.1) i.2
    mu := ![(3791359/50000000), (1/100000000), (245437/4000000), (1/100000000), (3637999/100000000), (1824181/100000000), (35867/50000000)]
    alternative := .zero
    polynomial := [(-20467591939554252808673744861912423161/8518971224691054991919012171500000000000), (27333007648733/30679625000000), (-293471810418832036429397436300198105563161/4259485612345527495959506085750000000000), (27333007648733/30679625000000), (-586923153245724518605986198855534298703161/8518971224691054991919012171500000000000)]
    bernstein := [(371264352574091327245580240835786852196427303159/1429246203344263628673035217078845440000000000000000), (127015404311682888555121296460960330326779360253/357311550836065907168258804269711360000000000000000), (113398537726079571862671577883991801216519577853/267983663127049430376194103202283520000000000000000), (10335243094273116695086555913138666868170559317/22331971927254119198016175266856960000000000000000), (2648634978082239133783241086051330690706173639/5582992981813529799504043816714240000000000000000)]
    reserve := (5195247/20000000000) }

theorem quarter_005_026_valid : quarter_005_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_026]
  · intro i; fin_cases i <;> norm_num [quarter_005_026]
  · norm_num [quarter_005_026]
  · norm_num [quarter_005_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_026]

def quarter_005_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/160), (3/320)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![(5061059/25000000), (5061059/25000000), (13649053/100000000), (13649053/100000000), (4829631/100000000), (5416709/100000000), (21967081/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (16637323/100000000), 0, 0]] i.1) i.2
    mu := ![(7548249/100000000), (1/100000000), (1533377/25000000), (1/100000000), (228649/6250000), (916867/50000000), (53283/50000000)]
    alternative := .zero
    polynomial := [(-320611078985658846112557623496753884509/86192250614444277964419600198000000000000), (136446296052201/153337700000000), (-1976974718064977698303967177184053730044509/43096125307222138982209800099000000000000), (136446296052201/153337700000000), (-3953628825050969737761821796744610706204509/86192250614444277964419600198000000000000)]
    bernstein := [(2824364760033818665114371133511812005075094691/56486953362682202006762029185761280000000000000000), (33581634075678960770510130125314313588193354473/112973906725364404013524058371522560000000000000000), (318483225511132201856500628526852088700418673457/677843440352186424081144350229135360000000000000000), (256580874464283885914314630433984178943121246257/451895626901457616054096233486090240000000000000000), (534199692257574067507268479309129020071900205971/903791253802915232108192466972180480000000000000000)]
    reserve := (25000151/500000000000) }

theorem quarter_005_027_valid : quarter_005_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_027]
  · intro i; fin_cases i <;> norm_num [quarter_005_027]
  · norm_num [quarter_005_027]
  · norm_num [quarter_005_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_027]

def quarter_005_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/320), (1/80)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![(20218379/100000000), (20218379/100000000), (13750149/100000000), (13750149/100000000), (4863127/100000000), (2726599/50000000), (21746619/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (16412437/100000000), 0, 0]] i.1) i.2
    mu := ![(750293/10000000), (1/100000000), (6124169/100000000), (1/100000000), (3685289/100000000), (1846249/100000000), (140983/100000000)]
    alternative := .zero
    polynomial := [(-11127359220103281104389503198868582336161/2203822625745828141938943926885500000000000), (544365663657693/612416900000000), (-37621670070118743024015616709823214781893661/1101911312872914070969471963442750000000000), (544365663657693/612416900000000), (-75232212781017382766926843916447560981451161/2203822625745828141938943926885500000000000)]
    bernstein := [(6558971987708712548044565811098882525213817540759/23108755136140574897617700670778900480000000000000000), (2762849182604384042138042450626032560547591325053/5777188784035143724404425167694725120000000000000000), (2673737187621883519463470497062977195837739719453/4332891588026357793303318875771043840000000000000000), (252882934634825047855056612080098905505434493717/361074299002196482775276572980920320000000000000000), (65722581892045276315799934603764732572539928039/90268574750549120693819143245230080000000000000000)]
    reserve := (141915303/500000000000) }

theorem quarter_005_028_valid : quarter_005_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_028]
  · intro i; fin_cases i <;> norm_num [quarter_005_028]
  · norm_num [quarter_005_028]
  · norm_num [quarter_005_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_028]

def quarter_005_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/80), (1/64)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![(20192961/100000000), (20192961/100000000), (173127/1250000), (173127/1250000), (2448003/50000000), (1097777/20000000), (5382217/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (126481/781250), 0, 0]] i.1) i.2
    mu := ![(1864583/25000000), (1/100000000), (6114653/100000000), (1/100000000), (927971/25000000), (464627/25000000), (10919/6250000)]
    alternative := .zero
    polynomial := [(-80534635624753833976925624878592874827/12629504745041531310108423124000000000000), (67869856916171/76433162500000), (-171326096029076149945054794414155689509827/6314752372520765655054211562000000000000), (67869856916171/76433162500000), (-342571657422527546056132663203432786144827/12629504745041531310108423124000000000000)]
    bernstein := [(250725843164845262205806270961221834129349573/517304514356901122462041011159040000000000000000), (268441529554205744516079459212488898878952133/413843611485520897969632808927232000000000000000), (763278963588438593402458963165971897698277967/993224667565250155127118741425356800000000000000), (223586119580053509975161849265011429691522501/264859911350733374700564997713428480000000000000), (185548908315010701690729238864792222111330757/211887929080586699760451998170742784000000000000)]
    reserve := (484677469/1000000000000) }

theorem quarter_005_029_valid : quarter_005_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_029]
  · intro i; fin_cases i <;> norm_num [quarter_005_029]
  · norm_num [quarter_005_029]
  · norm_num [quarter_005_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_029]

def quarter_005_030 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/64), (3/160)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![(1260499/6250000), (1260499/6250000), (13949097/100000000), (13949097/100000000), (492827/10000000), (5523773/100000000), (10656897/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (15968713/100000000), 0, 0]] i.1) i.2
    mu := ![(7414449/100000000), (1/100000000), (3052481/50000000), (1/100000000), (3738171/100000000), (935257/50000000), (41547/20000000)]
    alternative := .zero
    polynomial := [(-937793375102493645111709400011687271979/121758107402460111197775560323000000000000), (67695621250263/76312025000000), (-1367967182265570167817357735904438063347979/60879053701230055598887780161500000000000), (67695621250263/76312025000000), (-248636051923276167453600342037169494493089/11068918854769101017979596393000000000000)]
    bernstein := [(1378501218188913092205503295410448611292781589/2042762067642272216949099295060000768000000000000), (4185165097634596068455506551506339707354300991/5106905169105680542372748237650001920000000000000), (461432743253225095969878555945814388964737683/497425828159644208672670282887987200000000000000), (31892913175985012478468923123190565058455964727/31918157306910503389829676485312512000000000000000), (82525060207993109275507683775999733482991694501/79795393267276258474574191213281280000000000000000)]
    reserve := (168705553/250000000000) }

theorem quarter_005_030_valid : quarter_005_030.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_030]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_030]
  · intro i; fin_cases i <;> norm_num [quarter_005_030]
  · norm_num [quarter_005_030]
  · norm_num [quarter_005_030, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_030, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_030, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_030, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_030]

def quarter_005_031 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/160), (1/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![(2516419/12500000), (2516419/12500000), (14095521/100000000), (14095521/100000000), (31097/625000), (2787307/50000000), (524903/2500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (7820599/50000000), 0, 0]] i.1) i.2
    mu := ![(7349941/100000000), (1/100000000), (1219877/20000000), (1/100000000), (1888517/50000000), (118003/6250000), (54457/20000000)]
    alternative := .zero
    polynomial := [(-223741647024980078438251439393605693431/21761937136373108192532242079800000000000), (67486091705849/76242312500000), (-182613952715397369239590507719804226605431/10880968568186554096266121039900000000000), (67486091705849/76242312500000), (-365004163783769758400742764000214847517431/21761937136373108192532242079800000000000)]
    bernstein := [(5973112910934689469747505819276696530168035289/14261903121693480185057930169417728000000000000000), (153740150666552428891863862536133705549948577/187656620022282634013920133808128000000000000000), (2969704173046867335351610894723978806300224563/2674106835317527534698361906765824000000000000000), (15160609227589961802528546143052333211862553/11728538751392664625870008363008000000000000000), (76071084504028455546359404131184283918207369/55710559069115156972882539724288000000000000000)]
    reserve := (209407989/500000000000) }

theorem quarter_005_031_valid : quarter_005_031.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_031]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_031]
  · intro i; fin_cases i <;> norm_num [quarter_005_031]
  · norm_num [quarter_005_031]
  · norm_num [quarter_005_031, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_031, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_031, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_031, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_031]

def quarter_005_032 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (1/32)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![(20084073/100000000), (20084073/100000000), (14287119/100000000), (14287119/100000000), (5036399/100000000), (1409909/25000000), (20581581/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (7605757/50000000), 0, 0]] i.1) i.2
    mu := ![(7266347/100000000), (1/100000000), (3039561/50000000), (1/100000000), (3827807/100000000), (1910549/100000000), (5219/1562500)]
    alternative := .zero
    polynomial := [(-1137468032241086287149412237845279572889/88155834026415709298603097008000000000000), (8526657534277/9649400000000), (-9947780891929863991427139303274823953706613/749324589224533529038126324568000000000000), (8526657534277/9649400000000), (-19876224827311629515972738598506278154674113/1498649178449067058076252649136000000000000)]
    bernstein := [(3451247708700951112554644923774355123330084287/3836541896829611668675206781788160000000000000000), (545623102557371525387804090669321456119470921/438461931066241333562880775061504000000000000000), (3690225261142768832829708040114903419811329663/2455386813970951467952132340344422400000000000000), (18802010785734180818607421080734622659746161/11224625435295778139209747841574502400000000000), (4427281555266806166406445212553309574000047/2514316097506254303182983516512688537600000000)]
    reserve := (224893133/250000000000) }

theorem quarter_005_032_valid : quarter_005_032.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_032]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_032]
  · intro i; fin_cases i <;> norm_num [quarter_005_032]
  · norm_num [quarter_005_032]
  · norm_num [quarter_005_032, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_032, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_032, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_032, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_032]

def quarter_005_033 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/32), (3/80)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![(313103/1562500), (313103/1562500), (14474661/100000000), (14474661/100000000), (2547439/50000000), (2850761/50000000), (4035419/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2957957/20000000), 0, 0]] i.1) i.2
    mu := ![(143709/2000000), (1/100000000), (605821/10000000), (1/100000000), (969353/25000000), (386411/20000000), (98293/25000000)]
    alternative := .zero
    polynomial := [(-49739660653883916593924849239410826621/3205400652343277809764734391000000000000), (133631495879303/151455250000000), (-17545864829780730175727113678623172865371/1602700326171638904882367195500000000000), (133631495879303/151455250000000), (-35041989998907576434860302508006934904121/3205400652343277809764734391000000000000)]
    bernstein := [(571011412622029073742330347609059589843/413674608545415984326383523541811200000000), (51693901350921003008402909446216094135927/30555510858468226115016964807065600000000000), (17394748347738759701184608719410010740123611/9002963020798673766031784273510400000000000000), (10031958947048931830131762063377280571815063/4774298571635660330471400751104000000000000000), (22210194998864865235625206564060869812475923/10099477747690819929843347742720000000000000000)]
    reserve := (345084881/250000000000) }

theorem quarter_005_033_valid : quarter_005_033.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_033]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_033]
  · intro i; fin_cases i <;> norm_num [quarter_005_033]
  · norm_num [quarter_005_033]
  · norm_num [quarter_005_033, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_033, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_033, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_033, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_033]

def quarter_005_034 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/80), (1/20)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![(23629997/100000000), (23629997/100000000), (17202309/100000000), (17202309/100000000), (363253/6250000), (6322909/100000000), (6200431/100000000)]
    cone := fun i => (![![0, 0, 0, (8714783/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1065971/20000000), (1/100000000), (1423473/20000000), (1/100000000), (4588069/100000000), (434019/20000000), (161017/100000000)]
    alternative := .zero
    polynomial := [(-807320789199536412000951584474891933069/40543738410432829046702668101750000000000), (164917323743901/237245500000000), (-59746182440049275391043738617849893516819/20271869205216414523351334050875000000000), (164917323743901/237245500000000), (-118685044090899014370086525651224895100569/40543738410432829046702668101750000000000)]
    bernstein := [(3390215699756702369292194493329460079804225111/1660671525291328677752941285447680000000000000000), (1465641976325371292184133785889503470761343737/415167881322832169438235321361920000000000000000), (1539332891399790916655440351770759038445004837/311375910992124127078676491021440000000000000000), (163000716522364530714681015864331799155197593/25947992582677010589889707585120000000000000000), (48943234927098273189936815621021857738174231/6486998145669252647472426896280000000000000000)]
    reserve := (204147277/100000000000) }

theorem quarter_005_034_valid : quarter_005_034.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_034]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_034]
  · intro i; fin_cases i <;> norm_num [quarter_005_034]
  · norm_num [quarter_005_034]
  · norm_num [quarter_005_034, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_034, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_034, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_034, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_034]

def quarter_005_035 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![(24215409/100000000), (24215409/100000000), (887907/5000000), (887907/5000000), (5365699/100000000), (5419563/100000000), (5267639/100000000)]
    cone := fun i => (![![0, 0, 0, (1894777/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1316947/25000000), (1/100000000), (3608877/50000000), (1/100000000), (937497/20000000), (963523/50000000), (102781/50000000)]
    alternative := .zero
    polynomial := [(-316468056744173043490330562099004264481/13371226617320032854379690473000000000000), (21085902837703/30073975000000), (-12839296528407949924689197643190718536981/6685613308660016427189845236500000000000), (21085902837703/30073975000000), (-25362125000071726805888064724282432809481/13371226617320032854379690473000000000000)]
    bernstein := [(14256043487434755297803616594920318213445719/2139396258771205256700750475680000000000000000), (3840153591475758074403236834899156851262687/388981137958400955763772813760000000000000000), (17415642005617325863879474875358912321121327/1351197637118655951600473984640000000000000000), (24451271187065565307383552565532620388990183/1555924551833603823055091255040000000000000000), (628146285883446901438348057013369759217219239/34230340140339284107212007610880000000000000000)]
    reserve := (6663582507/1000000000000) }

theorem quarter_005_035_valid : quarter_005_035.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_035]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_035]
  · intro i; fin_cases i <;> norm_num [quarter_005_035]
  · norm_num [quarter_005_035]
  · norm_num [quarter_005_035, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_035, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_035, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_035, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_035]

def quarter_005_036 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![(28529849/100000000), (28529849/100000000), (21470151/100000000), (21470151/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, (3566231/25000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6359633/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2548739/50000000), (1/100000000), (8350627/100000000), (1/100000000), (5581079/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-14630873853509113986856822851469/475141113475308527548000000000000), (612540166037199/835062700000000), (-150187916064933289180424625371469/237570556737654263774000000000000), (612540166037199/835062700000000), (-285744958276357464373992427891469/475141113475308527548000000000000)]
    bernstein := [(25490257477659435824092235629782643811/1216361250496789830522880000000000000000), (7608049114191625794006234531462930737/304090312624197457630720000000000000000), (2207023450608842976077672870189828879/76022578156049364407680000000000000000), (627084715392320475293775086712237293/19005644539012341101920000000000000000), (175381556587630533180831912270724731/4751411134753085275480000000000000000)]
    reserve := (10478078559/500000000000) }

theorem quarter_005_036_valid : quarter_005_036.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_036]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_036]
  · intro i; fin_cases i <;> norm_num [quarter_005_036]
  · norm_num [quarter_005_036]
  · norm_num [quarter_005_036, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_036, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_036, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_036, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_036]

def quarter_005_037 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![(28221143/100000000), (28221143/100000000), (21778857/100000000), (21778857/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, (14110571/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3225537/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5042321/100000000), (1/100000000), (202473/2500000), (1/100000000), (226453/4000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-7655406841808595779855693567/231193535360762349000000000000), (68291581974839/89988000000000), (-72900865062724904181304763567/115596767680381174500000000000), (68291581974839/89988000000000), (-138146323283641212582753833567/231193535360762349000000000000)]
    bernstein := [(85934106388235089063946607440533/2311935353607623490000000000000000), (1412915096781157339992650709037/34250894127520348000000000000000), (201031198985858575754495109516721/4438915878926637100800000000000000), (1687922114991161094443821927/34250894127520348000000000000), (2016360928467476681156479150777/37878748833507303260160000000000)]
    reserve := (37169770449/1000000000000) }

theorem quarter_005_037_valid : quarter_005_037.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_037]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_037]
  · intro i; fin_cases i <;> norm_num [quarter_005_037]
  · norm_num [quarter_005_037]
  · norm_num [quarter_005_037, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_037, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_037, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_037, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_037]

def quarter_005_038 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![0, (38920699/100000000), (610793/2000000), (610793/2000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(389207/20000000), 0, (38920699/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2261523/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1363039/12500000), (1/100000000), (3969329/50000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-35948678385398736845663/519393622159776000000000), (766854532397/703504000000), (-238100306691402452879903/259696811079888000000000), (766854532397/703504000000), (-440251934997406168914143/519393622159776000000000)]
    bernstein := [(71534110978546154924297/1309191554687041536000000), (4933862248077388824685363/81824472167940096000000000), (375502778455266131363692093/5698490025981542400000000000), (2374536304449554913482944219/33241191818225664000000000000), (6391918330316596240718292817/83102979545564160000000000000)]
    reserve := (13659977931/250000000000) }

theorem quarter_005_038_valid : quarter_005_038.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_038]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_038]
  · intro i; fin_cases i <;> norm_num [quarter_005_038]
  · norm_num [quarter_005_038]
  · norm_num [quarter_005_038, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_038, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_038, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_038, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_038]

def quarter_005_039 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![0, (19300679/50000000), (30699321/100000000), (30699321/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(482517/25000000), 0, (19300679/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9093387/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (5265723/50000000), (1/100000000), (7980163/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-12457616137553962782672239/168085311411396000000000000), (197505913379653/175524100000000), (-77340828940881785540352239/84042655705698000000000000), (197505913379653/175524100000000), (-142224041744209608298032239/168085311411396000000000000)]
    bernstein := [(2079793107036981738272932227841/26893649825823360000000000000000), (4466741517946037403638466698429/53787299651646720000000000000000), (28625626747533343538439367081003/322723797909880320000000000000000), (20289219141514199617669760906869/215149198606586880000000000000000), (42967635789486593528298871278961/430298397213173760000000000000000)]
    reserve := (77333984807/1000000000000) }

theorem quarter_005_039_valid : quarter_005_039.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_039]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_039]
  · intro i; fin_cases i <;> norm_num [quarter_005_039]
  · norm_num [quarter_005_039]
  · norm_num [quarter_005_039, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_039, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_039, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_039, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_039]

def quarter_005_040 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![0, (38275717/100000000), (15431071/50000000), (15431071/50000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(956893/50000000), 0, (38275717/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (571351/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (2031009/20000000), (1/100000000), (1002811/12500000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-218167323388092266674921/2715624221732000000000000), (590635306602907/507752250000000), (-1257591965281685085114921/1357812110866000000000000), (590635306602907/507752250000000), (-2297016607175277903554921/2715624221732000000000000)]
    bernstein := [(2091953746548771609039760825637/20855994022901760000000000000000), (92203895318036779863681021097/868999750954240000000000000000), (3037513232078093544579758099/27156242217320000000000000000), (798095800879717535017567589/6789060554330000000000000000), (156845308882266342096695053/1272948853936875000000000000)]
    reserve := (100304677123/1000000000000) }

theorem quarter_005_040_valid : quarter_005_040.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_040]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_040]
  · intro i; fin_cases i <;> norm_num [quarter_005_040]
  · norm_num [quarter_005_040]
  · norm_num [quarter_005_040, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_040, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_040, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_040, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_040]

def quarter_005_041 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![0, (3794859/10000000), (6205141/20000000), (6205141/20000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1897429/100000000), 0, (3794859/10000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1838013/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (9776501/100000000), (1/100000000), (4032503/50000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-83301152114362114265431159/946170470688072000000000000), (23547635170119/19553002000000), (-442359504736848736450231159/473085235344036000000000000), (23547635170119/19553002000000), (-801417857359335358635031159/946170470688072000000000000)]
    bernstein := [(18287151400480523964969734129/147839136045011250000000000000), (16137103192512857152870544263/124496114564220000000000000000), (3846156684558971687814771513047/28385114120642160000000000000000), (2252285158014844111752443838931/15935502664220160000000000000000), (356393582469622046871897317113001/2422196404961464320000000000000000)]
    reserve := (61848140789/500000000000) }

theorem quarter_005_041_valid : quarter_005_041.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_041]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_041]
  · intro i; fin_cases i <;> norm_num [quarter_005_041]
  · norm_num [quarter_005_041]
  · norm_num [quarter_005_041, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_041, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_041, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_041, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_041]

def quarter_005_042 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![0, (37623949/100000000), (1247521/4000000), (1247521/4000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1881197/100000000), 0, (37623949/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4619073/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (9397071/100000000), (1/100000000), (5067/62500), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-10992466565673409051661/112865087424000000000000), (46936666480429/37588284000000), (-53456769496884582811661/56432543712000000000000), (46936666480429/37588284000000), (-95921072428095756571661/112865087424000000000000)]
    bernstein := [(42662276558871550727138640979/288934623805440000000000000000), (13326002306016362546608994513/86680387141632000000000000000), (1385004817804155829471783961/8668038714163200000000000000), (143709844023331523083573841/866803871416320000000000000), (14888946021165516004689913/86680387141632000000000000)]
    reserve := (147653735633/1000000000000) }

theorem quarter_005_042_valid : quarter_005_042.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_042]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_042]
  · intro i; fin_cases i <;> norm_num [quarter_005_042]
  · norm_num [quarter_005_042]
  · norm_num [quarter_005_042, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_042, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_042, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_042, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_042]

def quarter_005_043 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![0, (9326257/25000000), (15673743/50000000), (15673743/50000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1865251/100000000), 0, (9326257/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9285379/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (4508941/50000000), (1/100000000), (8148651/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-5319720875589001917391239/48989048784788000000000000), (146177355369951/112723525000000), (-23595099241687825058031239/24494524392394000000000000), (146177355369951/112723525000000), (-41870477607786648198671239/48989048784788000000000000)]
    bernstein := [(2161135466766834344685131929/12541196488905728000000000000), (22398992831913094271639828227/125411964889057280000000000000), (695476964305009053854877921379/3762358946671718400000000000000), (2396228917672216159445022723451/12541196488905728000000000000000), (24738338635393261459885119609001/125411964889057280000000000000000)]
    reserve := (34464581887/200000000000) }

theorem quarter_005_043_valid : quarter_005_043.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_043]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_043]
  · intro i; fin_cases i <;> norm_num [quarter_005_043]
  · norm_num [quarter_005_043]
  · norm_num [quarter_005_043, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_043, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_043, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_043, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_043]

def quarter_005_044 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![0, (18497209/50000000), (31502791/100000000), (31502791/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1849721/100000000), 0, (18497209/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4665691/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (8639939/100000000), (1/100000000), (4094511/50000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-8620129557683961896953993/70752650549658000000000000), (582713709210319/431996950000000), (-34794660848103739987393993/35376325274829000000000000), (582713709210319/431996950000000), (-60969192138523518077833993/70752650549658000000000000)]
    bernstein := [(35836121135881466594900262738887/181126785407124480000000000000000), (9254003883535920909843599554351/45281696351781120000000000000000), (7160807188386803798463834659969/33961272263835840000000000000000), (615019894650041213663799532379/2830106021986320000000000000000), (158309152474742025727223529167/707526505496580000000000000000)]
    reserve := (39570206091/200000000000) }

theorem quarter_005_044_valid : quarter_005_044.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_044]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_044]
  · intro i; fin_cases i <;> norm_num [quarter_005_044]
  · norm_num [quarter_005_044]
  · norm_num [quarter_005_044, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_044, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_044, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_044, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_044]

def quarter_005_045 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![0, (18347079/50000000), (31652921/100000000), (31652921/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(458677/25000000), 0, (18347079/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9375851/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1652827/20000000), (1/100000000), (514253/6250000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-22416600006866766580804681/163194478700352000000000000), (15695638977507/11167750000000), (-82299439868450276016964681/81597239350176000000000000), (15695638977507/11167750000000), (-142182279730033785453124681/163194478700352000000000000)]
    bernstein := [(366187341137210436331360385039/1631944787003520000000000000000), (1509042595285333601704661449469/6527779148014080000000000000000), (18638282272836485630623218590897/78333349776168960000000000000000), (25555221205042992801932361897529/104444466368225280000000000000000), (105029309429560144952754414821159/417777865472901120000000000000000)]
    reserve := (56096772399/250000000000) }

theorem quarter_005_045_valid : quarter_005_045.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_045]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_045]
  · intro i; fin_cases i <;> norm_num [quarter_005_045]
  · norm_num [quarter_005_045]
  · norm_num [quarter_005_045, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_045, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_045, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_045, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_045]

def quarter_005_046 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![0, (36405811/100000000), (6359419/20000000), (6359419/20000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1820291/100000000), 0, (36405811/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9418557/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (7891253/100000000), (1/100000000), (330621/4000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-270347461424974101335953/1739342638742000000000000), (231519806183809/157825060000000), (-903569255127799398955953/869671319371000000000000), (231519806183809/157825060000000), (-1536791048830624696575953/1739342638742000000000000)]
    bernstein := [(1122451276963051263800119143967/4452717155179520000000000000000), (577020514566640413942499476413/2226358577589760000000000000000), (296388138174701441262521396007/1113179288794880000000000000000), (152123923059908922026598318773/556589644397440000000000000000), (78022595281454633229113299247/278294822198720000000000000000)]
    reserve := (63020580347/250000000000) }

theorem quarter_005_046_valid : quarter_005_046.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_046]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_046]
  · intro i; fin_cases i <;> norm_num [quarter_005_046]
  · norm_num [quarter_005_046]
  · norm_num [quarter_005_046, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_046, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_046, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_046, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_046]

def quarter_005_047 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 0, 0, 0, 0, 2, 1]
    lambda := ![0, (18065267/50000000), (31934733/100000000), (31934733/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1806527/100000000), 0, (18065267/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4729663/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (7521979/100000000), (1/100000000), (1037663/12500000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-33033068582385389662375369/187326703081848000000000000), (576909478218711/376098950000000), (-100715206730451529130695369/93663351540924000000000000), (576909478218711/376098950000000), (-168397344878517668599015369/187326703081848000000000000)]
    bernstein := [(8424924075555363969161956994231/29972272493095680000000000000000), (3459195350074546588027607016739/11988908997238272000000000000000), (4257917371100188346554632722669/14386690796685926400000000000000), (581950384830825093161923369403/1918225439558123520000000000000), (238462740826374681457846458599/767290175823249408000000000000)]
    reserve := (28109060057/100000000000) }

theorem quarter_005_047_valid : quarter_005_047.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_005_047]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_005_047]
  · intro i; fin_cases i <;> norm_num [quarter_005_047]
  · norm_num [quarter_005_047]
  · norm_num [quarter_005_047, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_005_047, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_005_047, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_005_047, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_005_047]

def quarterTable005 : OwnerTable where
  mode := .quarter
  owners := ![0, 0, 0, 0, 0, 2, 1]
  rows := [quarter_005_000, quarter_005_001, quarter_005_002, quarter_005_003, quarter_005_004, quarter_005_005, quarter_005_006, quarter_005_007, quarter_005_008, quarter_005_009, quarter_005_010, quarter_005_011, quarter_005_012, quarter_005_013, quarter_005_014, quarter_005_015, quarter_005_016, quarter_005_017, quarter_005_018, quarter_005_019, quarter_005_020, quarter_005_021, quarter_005_022, quarter_005_023, quarter_005_024, quarter_005_025, quarter_005_026, quarter_005_027, quarter_005_028, quarter_005_029, quarter_005_030, quarter_005_031, quarter_005_032, quarter_005_033, quarter_005_034, quarter_005_035, quarter_005_036, quarter_005_037, quarter_005_038, quarter_005_039, quarter_005_040, quarter_005_041, quarter_005_042, quarter_005_043, quarter_005_044, quarter_005_045, quarter_005_046, quarter_005_047]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_005_000_valid
    · exact quarter_005_001_valid
    · exact quarter_005_002_valid
    · exact quarter_005_003_valid
    · exact quarter_005_004_valid
    · exact quarter_005_005_valid
    · exact quarter_005_006_valid
    · exact quarter_005_007_valid
    · exact quarter_005_008_valid
    · exact quarter_005_009_valid
    · exact quarter_005_010_valid
    · exact quarter_005_011_valid
    · exact quarter_005_012_valid
    · exact quarter_005_013_valid
    · exact quarter_005_014_valid
    · exact quarter_005_015_valid
    · exact quarter_005_016_valid
    · exact quarter_005_017_valid
    · exact quarter_005_018_valid
    · exact quarter_005_019_valid
    · exact quarter_005_020_valid
    · exact quarter_005_021_valid
    · exact quarter_005_022_valid
    · exact quarter_005_023_valid
    · exact quarter_005_024_valid
    · exact quarter_005_025_valid
    · exact quarter_005_026_valid
    · exact quarter_005_027_valid
    · exact quarter_005_028_valid
    · exact quarter_005_029_valid
    · exact quarter_005_030_valid
    · exact quarter_005_031_valid
    · exact quarter_005_032_valid
    · exact quarter_005_033_valid
    · exact quarter_005_034_valid
    · exact quarter_005_035_valid
    · exact quarter_005_036_valid
    · exact quarter_005_037_valid
    · exact quarter_005_038_valid
    · exact quarter_005_039_valid
    · exact quarter_005_040_valid
    · exact quarter_005_041_valid
    · exact quarter_005_042_valid
    · exact quarter_005_043_valid
    · exact quarter_005_044_valid
    · exact quarter_005_045_valid
    · exact quarter_005_046_valid
    · exact quarter_005_047_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
