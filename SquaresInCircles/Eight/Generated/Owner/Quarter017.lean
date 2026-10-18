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

def quarter_017_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(64079547/100000000), 0, (19192791/25000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (560543/100000000)]
    alternative := .zero
    polynomial := [(-519393814501857258543526403/25500310721794000000000000), (-64079547/560543), (-2265636775767813258543526403/12750155360897000000000000), (-64079547/560543), (-4011879737033769258543526403/25500310721794000000000000)]
    bernstein := [(44871879381266837221547798413/104449272716468224000000000000), (118565569597822284864385637161/261123181791170560000000000000), (900041480821549954429898111503/1958423863433779200000000000000), (728898063109215933426152754593/1632019886194816000000000000000), (1695751689872377268366533628797/4080049715487040000000000000000)]
    reserve := (20781017489/50000000000) }

theorem quarter_017_000_valid : quarter_017_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_000]
  · intro i; fin_cases i <;> norm_num [quarter_017_000]
  · norm_num [quarter_017_000]
  · norm_num [quarter_017_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_000]

def quarter_017_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(60597559/100000000), 0, (19887081/25000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (71153/12500000)]
    alternative := .zero
    polynomial := [(-3567884787796576400012997/202306469885875000000000), (-60597559/569224), (-17703919647340295150012997/101153234942937500000000), (-60597559/569224), (-31839954506884013900012997/202306469885875000000000)]
    bernstein := [(12501935583001258430979791803/32369035181740000000000000000), (26592731454965382940325433177/64738070363480000000000000000), (53950080917615703513363529043/129476140726960000000000000000), (104718388261650603138289401537/258952281453920000000000000000), (193849761346793175966427695083/517904562907840000000000000000)]
    reserve := (74859259883/200000000000) }

theorem quarter_017_001_valid : quarter_017_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_001]
  · intro i; fin_cases i <;> norm_num [quarter_017_001]
  · norm_num [quarter_017_001]
  · norm_num [quarter_017_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_001]

def quarter_017_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(28469751/50000000), 0, (41103203/50000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (577517/100000000)]
    alternative := .zero
    polynomial := [(-198390637679986255814753033/13136247305843000000000000), (-56939502/577517), (-1133327340271023255814753033/6568123652921500000000000), (-56939502/577517), (-2068264042862060255814753033/13136247305843000000000000)]
    bernstein := [(11527812398842346443288633898087/33628793102958080000000000000000), (3089044506232968121565127349497/8407198275739520000000000000000), (2356369666203460441793466878321/6305398706804640000000000000000), (190236389246127754008252617917/525449892233720000000000000000), (43716866270860360664919214927/131362473058430000000000000000)]
    reserve := (41599462591/125000000000) }

theorem quarter_017_002_valid : quarter_017_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_002]
  · intro i; fin_cases i <;> norm_num [quarter_017_002]
  · norm_num [quarter_017_002]
  · norm_num [quarter_017_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_002]

def quarter_017_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(53110117/100000000), 0, (84730841/100000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (585377/100000000)]
    alternative := .zero
    polynomial := [(-340003764663742932710239531/26630062973566000000000000), (-53110117/585377), (-2267298167786181932710239531/13315031486783000000000000), (-53110117/585377), (-4194592570908620932710239531/26630062973566000000000000)]
    bernstein := [(79690490161174118469644132189/266300629735660000000000000000), (345095618111994513874824855393/1065202518942640000000000000000), (1408630571095557185999559254641/4260810075770560000000000000000), (5445712097213912795858473175517/17043240303082240000000000000000), (536280456569952094069498304417/1842512465198080000000000000000)]
    reserve := (291059337019/1000000000000) }

theorem quarter_017_003_valid : quarter_017_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_003]
  · intro i; fin_cases i <;> norm_num [quarter_017_003]
  · norm_num [quarter_017_003]
  · norm_num [quarter_017_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_003]

def quarter_017_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(24557813/50000000), 0, (21776787/25000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (592757/100000000)]
    alternative := .zero
    polynomial := [(-143343884427826251024359563/13482897549803000000000000), (-49115626/592757), (-1134016919364172251024359563/6741448774901500000000000), (-49115626/592757), (-2124689954300518251024359563/13482897549803000000000000)]
    bernstein := [(8820091375988401027759847564517/34516217727495680000000000000000), (967635282974101041790199845167/3451621772749568000000000000000), (297494973461131953373716301943/1035486531824870400000000000000), (9552729943284566272186750359/34516217727495680000000000000), (859512033393321453960086293/3451621772749568000000000000)]
    reserve := (249016865109/1000000000000) }

theorem quarter_017_004_valid : quarter_017_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_004]
  · intro i; fin_cases i <;> norm_num [quarter_017_004]
  · norm_num [quarter_017_004]
  · norm_num [quarter_017_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_004]

def quarter_017_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(44963763/100000000), 0, (44660553/50000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (299807/50000000)]
    alternative := .zero
    polynomial := [(-118578646771640548454882503/13638867413506000000000000), (-44963763/599614), (-1134431113493327548454882503/6819433706753000000000000), (-44963763/599614), (-2150283580215014548454882503/13638867413506000000000000)]
    bernstein := [(738739977257359496538956633/3491550057857536000000000000), (8256344367311587289122568881/34915500578575360000000000000), (255293416136960765965024375403/1047465017357260800000000000000), (815898362708370707000884605233/3491550057857536000000000000000), (7213078694035214263582763440217/34915500578575360000000000000000)]
    reserve := (41317343727/200000000000) }

theorem quarter_017_005_valid : quarter_017_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_005]
  · intro i; fin_cases i <;> norm_num [quarter_017_005]
  · norm_num [quarter_017_005]
  · norm_num [quarter_017_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_005]

def quarter_017_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1270743/3125000), 0, (22839737/25000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (37869/6250000)]
    alternative := .zero
    polynomial := [(-1497850999510546586193607/215342816412750000000000), (-847162/12623), (-17732677941423765336193607/107671408206375000000000), (-847162/12623), (-11322501627778994695397869/71780938804250000000000)]
    bernstein := [(7094624971197313201035914621/42405970001280000000000000000), (13248595199800887356686246297/68909701252080000000000000000), (99284856039911855952429187/496944960952500000000000000), (34129240290295240728989927/179452347010625000000000000), (423635897820925629483109/2588255004960937500000000)]
    reserve := (163676259491/1000000000000) }

theorem quarter_017_006_valid : quarter_017_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_006]
  · intro i; fin_cases i <;> norm_num [quarter_017_006]
  · norm_num [quarter_017_006]
  · norm_num [quarter_017_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_006]

def quarter_017_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7245283/20000000), 0, (93207547/100000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (611587/100000000)]
    alternative := .zero
    polynomial := [(-150687422572205627852459171/27822412434746000000000000), (-36226415/611587), (-2270793650030418627852459171/13911206217373000000000000), (-36226415/611587), (-4390899877488631627852459171/27822412434746000000000000)]
    bernstein := [(533022964331504892934400101/4347251942929062500000000000), (10268426581741151949032370839/69556031086865000000000000000), (43235408984956686979468288849/278224124347460000000000000000), (1301485363751958291458029193347/8903171979118720000000000000000), (8559979570496087711965169757629/71225375832949760000000000000000)]
    reserve := (120181599189/1000000000000) }

theorem quarter_017_007_valid : quarter_017_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_007]
  · intro i; fin_cases i <;> norm_num [quarter_017_007]
  · norm_num [quarter_017_007]
  · norm_num [quarter_017_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_007]

def quarter_017_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7915969/25000000), 0, (4742731/5000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (616623/100000000)]
    alternative := .zero
    polynomial := [(-28580283563198360088284407/7012877735608500000000000), (-31663876/616623), (-189324317857314453362761469/1168812955934750000000000), (-31663876/616623), (-1107365623580688360088284407/7012877735608500000000000)]
    bernstein := [(1389602794071461999576952201193/17952967003157760000000000000000), (919762875047625900038009555597/8976483501578880000000000000000), (495671228434459756387585433713/4488241750789440000000000000000), (227903837404947184315067257877/2244120875394720000000000000000), (85262884701077516071696112633/1122060437697360000000000000000)]
    reserve := (37993891343/500000000000) }

theorem quarter_017_008_valid : quarter_017_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_008]
  · intro i; fin_cases i <;> norm_num [quarter_017_008]
  · norm_num [quarter_017_008]
  · norm_num [quarter_017_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_008]

def quarter_017_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(13494863/50000000), 0, (96288913/100000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (31049/5000000)]
    alternative := .zero
    polynomial := [(-258992654029465431307083/88280375858875000000000), (-13494863/310490), (-7103352722536112306307083/44140187929437500000000), (-13494863/310490), (-13947712791042759181307083/88280375858875000000000)]
    bernstein := [(445784718876353641769848677/14124860137420000000000000000), (320062703856344572300697639/5649944054968000000000000000), (439269635714821213655421991/6779932865961600000000000000), (10157849188001732310291123/180798209758976000000000000), (447926284751798359102973/14463856780718080000000000)]
    reserve := (7742165377/250000000000) }

theorem quarter_017_009_valid : quarter_017_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_009]
  · intro i; fin_cases i <;> norm_num [quarter_017_009]
  · norm_num [quarter_017_009]
  · norm_num [quarter_017_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_009]

def quarter_017_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-9/80)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(4683949/20000000), 0, (19443781/20000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (311681/100000000)]
    alternative := .zero
    polynomial := [(-12557362422667860850450339/2835808259519600000000000), (-23419745/311681), (-454827141107366860850450339/1417904129759800000000000), (-23419745/311681), (-897096919792065860850450339/2835808259519600000000000)]
    bernstein := [(10128219225090316273892709/464618825239691264000000000), (796994745739179204750489857/23230941261984563200000000000), (133893547118992016693971466887/3484641189297684480000000000000), (397119764232257448522148058709/11615470630992281600000000000000), (2513024157083107562767398410621/116154706309922816000000000000000)]
    reserve := (21635147097/1000000000000) }

theorem quarter_017_010_valid : quarter_017_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_010]
  · intro i; fin_cases i <;> norm_num [quarter_017_010]
  · norm_num [quarter_017_010]
  · norm_num [quarter_017_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_010]

def quarter_017_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/80), (-17/160)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(4323281/20000000), 0, (48817853/50000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (15611/10000000)]
    alternative := .zero
    polynomial := [(-5361945393440661688632157/710178078538000000000000), (-4323281/31222), (-227444893583118061688632157/355089039269000000000000), (-4323281/31222), (-449527841772795461688632157/710178078538000000000000)]
    bernstein := [(485633885813777530713913320323/29088894096916480000000000000000), (1334653790459184166264051726299/58177788193832960000000000000000), (8729560977720549654604077452761/349066729162997760000000000000000), (5330426553193760738906038441931/232711152775331840000000000000000), (7745254197617368707981041397603/465422305550663680000000000000000)]
    reserve := (3328269447/200000000000) }

theorem quarter_017_011_valid : quarter_017_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_011]
  · intro i; fin_cases i <;> norm_num [quarter_017_011]
  · norm_num [quarter_017_011]
  · norm_num [quarter_017_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_011]

def quarter_017_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-17/160), (-1/10)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(20001281/100000000), (9259939/50000000), (2288697/20000000), (2288697/20000000), (948427/25000000), (4141921/100000000), (15328121/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1251263/20000000), 0, (12934569/50000000), 0, 0]] i.1) i.2
    mu := ![(9249111/100000000), (109369/10000000), (5500881/100000000), (1/100000000), (1523147/50000000), (1419237/100000000), (599/1250000)]
    alternative := .zero
    polynomial := [(-182311524793790133758480657823436350020435171/88953907565613999138199386317199000000000000), (-774280207103/19168000000), (-4436087689698816468778819480084292892804883273/22238476891403499784549846579299750000000000), (-774280207103/19168000000), (-17562039234001475741356797262513735221199097921/88953907565613999138199386317199000000000000)]
    bernstein := [(802871398088689275369575507054171066581119043127359/58296832862200790475210349816839536640000000000000000), (9856580020086236471122887729299618839736119643567/607258675647924900783441143925411840000000000000000), (11879227907169561091376261604819217514393415141943/683166010103915513381371286916088320000000000000000), (20455190461277401862677223242384145833255912639/1186052100874853321842658484229320000000000000000), (14061388631060847087073815761884198467371820379/889539075656139991381993863171990000000000000000)]
    reserve := (13772127209/1000000000000) }

theorem quarter_017_012_valid : quarter_017_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_012]
  · intro i; fin_cases i <;> norm_num [quarter_017_012]
  · norm_num [quarter_017_012]
  · norm_num [quarter_017_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_012]

def quarter_017_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-7/80)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(20050517/100000000), (935323/5000000), (11644233/100000000), (11644233/100000000), (3889931/100000000), (852027/20000000), (29804491/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(2769827/50000000), 0, (25025013/100000000), 0, 0]] i.1) i.2
    mu := ![(9076563/100000000), (128923/12500000), (5567681/100000000), (1/100000000), (3102101/100000000), (182211/12500000), (9337/10000000)]
    alternative := .zero
    polynomial := [(-647790633277970976820147068153275849392371229/790450722738279958888198481677218000000000000), (-84299906063257/4668500000000), (-39030999305068532014253267969216684704134372229/395225361369139979444099240838609000000000000), (-84299906063257/4668500000000), (-77414207976859093051686388870280093558876373229/790450722738279958888198481677218000000000000)]
    bernstein := [(54517060201516649627905217271071362112174850971/7904507227382799588881984816772180000000000000000), (247091577504642748722554664590555142308527311299/21078685939687465570351959511392480000000000000000), (3027524087686690915372667128698601021402351148291/216809341093928217295048726402894080000000000000000), (18390355345963122355255733018238655522714324192151/1349035900139997796502525408729118720000000000000000), (347563890040320678113065025350156630042633228248371/32376861603359947116060609809498849280000000000000000)]
    reserve := (6896958739/1000000000000) }

theorem quarter_017_013_valid : quarter_017_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_013]
  · intro i; fin_cases i <;> norm_num [quarter_017_013]
  · norm_num [quarter_017_013]
  · norm_num [quarter_017_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_013]

def quarter_017_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/80), (-3/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(4021549/20000000), (9472931/50000000), (11904417/100000000), (11904417/100000000), (4015603/100000000), (883029/20000000), (28706811/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(4634263/100000000), 0, (5978783/25000000), 0, 0]] i.1) i.2
    mu := ![(8856073/100000000), (908531/100000000), (5653829/100000000), (1/100000000), (793633/25000000), (1508027/100000000), (2253/2500000)]
    alternative := .zero
    polynomial := [(-72719933704908429221338660669202105392298136163/122663014717389263742521397674918121000000000000), (-45483238077391/3004000000000), (-2932321743845357381432035263741084336195347866769/30665753679347315935630349418729530250000000000), (-45483238077391/3004000000000), (-685680414216265946853341317311478543493476078289/7215471453964074337795376333818713000000000000)]
    bernstein := [(22365014436604632774969297972240978700029296765424287/5024277082824264242893676448764646236160000000000000000), (22956944884799114221828611885015311840658965245547423/2512138541412132121446838224382323118080000000000000000), (42675283161303557625837201784574513368205173965954701/3768207812118198182170257336573484677120000000000000000), (6921116149296079136134206279047675670552170206433743/628034635353033030361709556095580779520000000000000000), (2584521222612042239260004809901045962626943186491647/314017317676516515180854778047790389760000000000000000)]
    reserve := (139105923/31250000000) }

theorem quarter_017_014_valid : quarter_017_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_014]
  · intro i; fin_cases i <;> norm_num [quarter_017_014]
  · norm_num [quarter_017_014]
  · norm_num [quarter_017_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_014]

def quarter_017_015 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/16)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(20156341/100000000), (19175519/100000000), (3039017/25000000), (3039017/25000000), (1034507/25000000), (4566761/100000000), (27651213/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(946039/25000000), 0, (22824291/100000000), 0, 0]] i.1) i.2
    mu := ![(864619/10000000), (7833/1000000), (5736841/100000000), (1/100000000), (811171/25000000), (778593/50000000), (43481/50000000)]
    alternative := .zero
    polynomial := [(-5195974281199320018208534945446022601192251/12701905084513922562260024075045250000000000), (-13496448318473/1087025000000), (-56159072638182079411775177574870067931670337/604852623072091550583810670240250000000000), (-13496448318473/1087025000000), (-587072275560312173814535097063412701981942413/6350952542256961281130012037522625000000000)]
    bernstein := [(35306914743361811309705789178175178206600630147/16258438508177820879692830816057920000000000000000), (43746659761730448102353949026477631762208529569/6503375403271128351877132326423168000000000000000), (1096966988651014733970728716595579178065001039/123873817205164349559564425265203200000000000000), (8912595457700128089000283387926686617324109737/1040540064523380536300341172227706880000000000000), (813215602349261250248867328592503355547130321/138738675269784071506712156297027584000000000000)]
    reserve := (434321103/200000000000) }

theorem quarter_017_015_valid : quarter_017_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_015]
  · intro i; fin_cases i <;> norm_num [quarter_017_015]
  · norm_num [quarter_017_015]
  · norm_num [quarter_017_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_015]

def quarter_017_016 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/16), (-1/20)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(5049329/25000000), (19396483/100000000), (309981/2500000), (309981/2500000), (1064239/25000000), (942911/20000000), (26636209/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1493561/50000000), 0, (21753629/100000000), 0, 0]] i.1) i.2
    mu := ![(4223271/50000000), (655933/100000000), (5816937/100000000), (1/100000000), (1656273/50000000), (20063/1250000), (83893/100000000)]
    alternative := .zero
    polynomial := [(-5277230656145381200561729835640334824815489819/19965205903982982224214237752391972000000000000), (-5176254012321/524331250000), (-903807037212851551503190571584008377663780369819/9982602951991491112107118876195986000000000000), (-5176254012321/524331250000), (-1802336843769557721805819413332376420502745249819/19965205903982982224214237752391972000000000000)]
    bernstein := [(69486425405105828663513469037890796262629904869/1308439734123428723046104285340760276992000000000000), (2444181476082586826425773510986276395445745467319/545183222551428634602543452225316782080000000000000), (40165162801684875387605378627303858685482664844159/6133311253703572139278613837534813798400000000000000), (5328903339130911184888428343067035303015846336167/851848785236607241566474144102057472000000000000000), (11526234705813901944552348687070206499158376654981/3194432944637277155874278040382715520000000000000000)]
    reserve := (13276581/250000000000) }

theorem quarter_017_016_valid : quarter_017_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_016]
  · intro i; fin_cases i <;> norm_num [quarter_017_016]
  · norm_num [quarter_017_016]
  · norm_num [quarter_017_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_016]

def quarter_017_017 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-7/160)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(20223611/100000000), (2444641/12500000), (2515221/20000000), (2515221/20000000), (2171859/50000000), (2411323/50000000), (25900687/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1211433/50000000), 0, (2096447/10000000), 0, 0]] i.1) i.2
    mu := ![(8303297/100000000), (529393/100000000), (587523/10000000), (1/100000000), (3361939/100000000), (328001/20000000), (2041/5000000)]
    alternative := .zero
    polynomial := [(-414668276851431034215550358053773307137559829/1162496454623492090387359409928083400000000000), (-32175268919431/2041000000000), (-99862099636148766692807274678126768680724732029/581248227311746045193679704964041700000000000), (-32175268919431/2041000000000), (-199309530995446102351398998998199764054311904229/1162496454623492090387359409928083400000000000)]
    bernstein := [(539667592752076537657625120930224930605504420571/185999432739758734461977505588493344000000000000000), (2511444507381442913049885248501530610511745579799/495998487306023291898606681569315584000000000000000), (218038846776393322187942132110655082436003815299137/35711891086033677016699681072990722048000000000000000), (191378741439314137494219550087139510246722429606151/31743903187585490681510827620436197376000000000000000), (283309544207992020986076536205057460564371485201767/58604128961696290488943066376189902848000000000000000)]
    reserve := (2901447519/1000000000000) }

theorem quarter_017_017_valid : quarter_017_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_017]
  · intro i; fin_cases i <;> norm_num [quarter_017_017]
  · norm_num [quarter_017_017]
  · norm_num [quarter_017_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_017]

def quarter_017_018 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/160), (-3/80)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(5059809/25000000), (19662049/100000000), (12691413/100000000), (12691413/100000000), (4400351/100000000), (4893303/100000000), (5084447/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(2062153/100000000), 0, (20445157/100000000), 0, 0]] i.1) i.2
    mu := ![(2052701/25000000), (464141/100000000), (369581/6250000), (1/100000000), (3394153/100000000), (12991/781250), (40087/100000000)]
    alternative := .zero
    polynomial := [(-74820455563866034292688657989464348367594673/284521281568189561946839389767689600000000000), (-54000923288481/4008700000000), (-24154476971209694609563953412607164359127786673/142260640784094780973419694883844800000000000), (-54000923288481/4008700000000), (-48234133486855523184835218167224864369887978673/284521281568189561946839389767689600000000000)]
    bernstein := [(354533532906587167726158696542243771674702742943727/186463867088528711317480662478153056256000000000000000), (376135168664579713303595278076430661693599032595083/93231933544264355658740331239076528128000000000000000), (707753861309517510993232129741289847075649170814021/139847900316396533488110496858614792192000000000000000), (116115286802911427771579539506200957906919063570003/23307983386066088914685082809769132032000000000000000), (44259866843349330245256682444946635839121018597887/11653991693033044457342541404884566016000000000000000)]
    reserve := (950676231/500000000000) }

theorem quarter_017_018_valid : quarter_017_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_018]
  · intro i; fin_cases i <;> norm_num [quarter_017_018]
  · norm_num [quarter_017_018]
  · norm_num [quarter_017_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_018]

def quarter_017_019 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/80), (-1/32)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(10126729/50000000), (9882689/50000000), (12804659/100000000), (12804659/100000000), (2227993/50000000), (155087/3125000), (24953077/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1713499/100000000), 0, (77857/390625), 0, 0]] i.1) i.2
    mu := ![(406033/5000000), (39847/10000000), (5950759/100000000), (1/100000000), (856449/25000000), (1685303/100000000), (7873/20000000)]
    alternative := .zero
    polynomial := [(-404594722954116312162164787295237280920737317/2188159983248525994787435784146158000000000000), (-44313200696363/3936500000000), (-184043769124381614711332329403792328945337797317/1094079991624262997393717892073079000000000000), (-44313200696363/3936500000000), (-367682943525809113110502494020289420609754857317/2188159983248525994787435784146158000000000000)]
    bernstein := [(84329873549274060207901707074855976825253892678923/89627032913859624746493369718626631680000000000000000), (9927523642721589028777906760022215038743755511851/3259164833231259081690667989768241152000000000000000), (174450685034822114614541458603935903157807082570329/43020975798652619878316817464940783206400000000000000), (2019063799348271075404982288210098186880160659/508747681284879466410250613036993740800000000000), (249606448836396916791724435401619292102352083/89539591906138786088204107894510898380800000000)]
    reserve := (940897749/1000000000000) }

theorem quarter_017_019_valid : quarter_017_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_019]
  · intro i; fin_cases i <;> norm_num [quarter_017_019]
  · norm_num [quarter_017_019]
  · norm_num [quarter_017_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_019]

def quarter_017_020 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/32), (-1/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(162131/800000), (19867241/100000000), (12915859/100000000), (12915859/100000000), (2255301/50000000), (2515521/50000000), (12246511/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(344161/25000000), 0, (9711631/50000000), 0, 0]] i.1) i.2
    mu := ![(502051/6250000), (83101/25000000), (1197529/20000000), (1/100000000), (3456871/100000000), (1707357/100000000), (19327/50000000)]
    alternative := .zero
    polynomial := [(-7644331253335659551635566690581817989723779/62800839805438658504935577023108000000000000), (-8813517111349/966350000000), (-5253619486139193185040004387946063903848978779/31400419902719329252467788511554000000000000), (-8813517111349/966350000000), (-10499594641025050710528373209201545989708233779/62800839805438658504935577023108000000000000)]
    bernstein := [(2049534583389965574038613576546245075772701/105362325439724234848754124180131990732800000000), (6907325368237264464589750575321669105727094741/3292572669991382339023566380629124710400000000000), (317545666515140729358307748484330408681799084429/102892895937230698094486449394660147200000000000000), (383938391030195236487481829311599241630978450701/128616119921538372618108061743325184000000000000000), (288619961925381426251782469222616895347562233421/160770149901922965772635077179156480000000000000000)]
    reserve := (4863063/250000000000) }

theorem quarter_017_020_valid : quarter_017_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_020]
  · intro i; fin_cases i <;> norm_num [quarter_017_020]
  · norm_num [quarter_017_020]
  · norm_num [quarter_017_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_020]

def quarter_017_021 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), (-7/320)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(316801/1562500), (19942751/100000000), (1624741/12500000), (1624741/12500000), (28443/625000), (79397/1562500), (24153841/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(113159/10000000), 0, (19045911/100000000), 0, 0]] i.1) i.2
    mu := ![(7968417/100000000), (267507/100000000), (6014949/100000000), (1/100000000), (695961/20000000), (1723627/100000000), (19063/100000000)]
    alternative := .zero
    polynomial := [(-602289333399817603443274693329735094217492429/3619708308240627186768655549474011000000000000), (-3511572782727/238287500000), (-193747368561877605270028159069340487504700889143/603284718040104531128109258245668500000000000), (-3511572782727/238287500000), (-1161881922037865814016725679722713189933987842429/3619708308240627186768655549474011000000000000)]
    bernstein := [(1451253307297948268261866844151149408162146549419/1029605918788445066458639800739274240000000000000000), (180557989269955520653052899112801717641740601686997/74131626152768044785022065653227745280000000000000000), (1742915103222855850547045938945017628151104394455379/593053009222144358280176525225821962240000000000000000), (1259166566700359095934190611888159329574760175944623/431311279434286806021946563800597790720000000000000000), (30076610021221686209734105381431846011632314110329057/12651797530072412976643765871484201861120000000000000000)]
    reserve := (1409523081/1000000000000) }

theorem quarter_017_021_valid : quarter_017_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_021]
  · intro i; fin_cases i <;> norm_num [quarter_017_021]
  · norm_num [quarter_017_021]
  · norm_num [quarter_017_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_021]

def quarter_017_022 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/320), (-3/160)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(20280831/100000000), (9996349/50000000), (13052011/100000000), (13052011/100000000), (2288701/50000000), (2557291/50000000), (4786093/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(485887/50000000), 0, (3759229/20000000), 0, 0]] i.1) i.2
    mu := ![(3963089/50000000), (46831/20000000), (3016493/50000000), (1/100000000), (1747459/50000000), (867171/50000000), (18889/100000000)]
    alternative := .zero
    polynomial := [(-49738626489989276661445911207732325594817/401783019674166059669785203884250000000000), (-923472609229/72650000000), (-64383462731774799109832053875250837697320067/200891509837083029834892601942125000000000), (-923472609229/72650000000), (-128717186837059608943002661839293943069045317/401783019674166059669785203884250000000000)]
    bernstein := [(4064607123399776103596601850189616009526600715483/4213000316378583501843046899481313280000000000000000), (4180429325706290951790776152041597685384548242407/2106500158189291750921523449740656640000000000000000), (7844175651501227302187218014249526618559645260009/3159750237283937626382285174610984960000000000000000), (1294903277773851266377538003210710225453729902287/526625039547322937730380862435164160000000000000000), (503887402613571034856508522014240027853056935723/263312519773661468865190431217582080000000000000000)]
    reserve := (30149291/31250000000) }

theorem quarter_017_022_valid : quarter_017_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_022]
  · intro i; fin_cases i <;> norm_num [quarter_017_022]
  · norm_num [quarter_017_022]
  · norm_num [quarter_017_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_022]

def quarter_017_023 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/160), (-1/64)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(20286123/100000000), (5010587/25000000), (6552797/50000000), (6552797/50000000), (4603657/100000000), (2573713/50000000), (23709259/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(162953/20000000), 0, (1854783/10000000), 0, 0]] i.1) i.2
    mu := ![(788449/10000000), (40143/20000000), (3025447/50000000), (1/100000000), (3509891/100000000), (34899/2000000), (18717/100000000)]
    alternative := .zero
    polynomial := [(-4284792822415622631004988226131196067764953/48786910924176159650800853708586000000000000), (-20067739664167/1871700000000), (-7820191254657698213972908052333401377531932953/24393455462088079825400426854293000000000000), (-20067739664167/1871700000000), (-5212032572164326935104937038813557186332033651/16262303641392053216933617902862000000000000)]
    bernstein := [(16936119973678856543117285605046762670793128200407/31972989943268087988748847486458920960000000000000000), (6579295848892763719144892027349764698282956874463/4263065325769078398499846331527856128000000000000000), (4461699186997435518550130356763101867455463199291/2192433596109811747799920970500040294400000000000000), (241334780072997460664880982617262757041328951461/120368903315832801839995661125492408320000000000000), (23321752195654760560052093918781071907027888573/16049187108777706911999421483398987776000000000000)]
    reserve := (10594017/20000000000) }

theorem quarter_017_023_valid : quarter_017_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_023]
  · intro i; fin_cases i <;> norm_num [quarter_017_023]
  · norm_num [quarter_017_023]
  · norm_num [quarter_017_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_023]

def quarter_017_024 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/64), (-1/80)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(20291151/100000000), (4018343/20000000), (13158679/100000000), (13158679/100000000), (2314821/50000000), (161873/3125000), (11745099/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(660531/100000000), 0, (9150487/50000000), 0, 0]] i.1) i.2
    mu := ![(490209/6250000), (167191/100000000), (6068677/100000000), (1/100000000), (3524723/100000000), (35109/2000000), (9273/50000000)]
    alternative := .zero
    polynomial := [(-14794109838361315830773759368666065120898211/253670165844656732381775486328308000000000000), (-2710207644653/309100000000), (-40829237793274686039415986097721187995386198211/126835082922328366190887743164154000000000000), (-2710207644653/309100000000), (-81643681476711010763001198436073709925651498211/253670165844656732381775486328308000000000000)]
    bernstein := [(26065429478753864577731493045703798494835877453/250345833243036967354308341037357072384000000000000), (38663605989090530524074865128558310918259743781/34770254617088467688098380699632926720000000000000), (31835151068414577199061215907847013415459837446231/19949433586554508336046445926414391705600000000000000), (130616740020528500355127074280168331996338300031/83962262569673856633192112484909056000000000000000), (10303394693117873531134682582168455103429860040989/10390329992997139758357523920007495680000000000000000)]
    reserve := (13014711/125000000000) }

theorem quarter_017_024_valid : quarter_017_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_024]
  · intro i; fin_cases i <;> norm_num [quarter_017_024]
  · norm_num [quarter_017_024]
  · norm_num [quarter_017_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_024]

def quarter_017_025 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/80), (-7/640)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(4058951/20000000), (10064283/50000000), (13198167/100000000), (13198167/100000000), (581119/12500000), (40657/781250), (364489/1562500)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(273329/50000000), 0, (3623359/20000000), 0, 0]] i.1) i.2
    mu := ![(7812839/100000000), (26879/20000000), (3040967/50000000), (1/100000000), (1767877/50000000), (881627/50000000), (9209/100000000)]
    alternative := .zero
    polynomial := [(-367862218865438444357348646649896840455894751/4583034162072872727417135597215648500000000000), (-3280695226339/230225000000), (-1423713294288745521139634384637963233245016709751/2291517081036436363708567798607824250000000000), (-3280695226339/230225000000), (-2847058726358625603834911420629276569649577524751/4583034162072872727417135597215648500000000000)]
    bernstein := [(148915821482379320825770837823108617728481755902449/187721079278504866915005874061952962560000000000000000), (1942594010380538772761636562760381507439450342750743/1501768634228038935320046992495623700480000000000000000), (55540205476105682072711019863758768043245698652584803/36042447221472934447681127819894968811520000000000000000), (147590035313139300134718170985388776002393826177314407/96113192590594491860483007519719916830720000000000000000), (982205310487721648891841422869706322284716390342772049/768905540724755934883864060157759334645760000000000000000)]
    reserve := (793282363/1000000000000) }

theorem quarter_017_025_valid : quarter_017_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_025]
  · intro i; fin_cases i <;> norm_num [quarter_017_025]
  · norm_num [quarter_017_025]
  · norm_num [quarter_017_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_025]

def quarter_017_026 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/640), (-3/320)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(20297081/100000000), (5038263/25000000), (13224339/100000000), (13224339/100000000), (233087/5000000), (20391/390625), (23219353/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(235797/50000000), 0, (4498617/25000000), 0, 0]] i.1) i.2
    mu := ![(7792669/100000000), (2939/2500000), (3045367/50000000), (1/100000000), (1771533/50000000), (1768421/100000000), (9167/100000000)]
    alternative := .zero
    polynomial := [(-18477595877843197333063443251875480144254749/308158561411379790316291268779878000000000000), (-226391872281/18334000000), (-95979528495156684161228411222883495502975197749/154079280705689895158145634389939000000000000), (-226391872281/18334000000), (-191940579394435525125123759002515115525806140749/308158561411379790316291268779878000000000000)]
    bernstein := [(30231373725310761250482046526116372761385410705162451/51700427470479836001711269352340696596480000000000000000), (28011212278433506649575200804966430394892583078686079/25850213735239918000855634676170348298240000000000000000), (51531141748332502300441992650346160239560586942016273/38775320602859877001283452014255522447360000000000000000), (8536175224949890697419620987913826821939616040512039/6462553433809979500213908669042587074560000000000000000), (3422912860832148839030397825020577766763921617402531/3231276716904989750106954334521293537280000000000000000)]
    reserve := (73092659/125000000000) }

theorem quarter_017_026_valid : quarter_017_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_026]
  · intro i; fin_cases i <;> norm_num [quarter_017_026]
  · norm_num [quarter_017_026]
  · norm_num [quarter_017_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_026]

def quarter_017_027 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/320), (-1/128)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(10149673/50000000), (5044369/25000000), (3312597/25000000), (3312597/25000000), (233723/5000000), (5236009/100000000), (23111933/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(397207/100000000), 0, (17872511/100000000), 0, 0]] i.1) i.2
    mu := ![(7772631/100000000), (3147/3125000), (1219901/20000000), (1/100000000), (1775171/50000000), (1773561/100000000), (73/800000)]
    alternative := .zero
    polynomial := [(-4067334165271671260204846660527925409977/95250237881556046739016196512375000000000), (-9548460508131/912500000000), (-119263582425085441095147895447562354479362133/190500475763112093478032393024750000000000), (-9548460508131/912500000000), (-39751815918918299250875828584747099542847393/63500158587704031159344131008250000000000)]
    bernstein := [(756204364198735646791611617957897730769994829101/1997542268737810265308212945483202560000000000000000), (700039518359775319220537757939653148391574215247/799016907495124106123285178193281024000000000000000), (1072850956951481628382234130947386386574332960143/958820288994148927347942213831937228800000000000000), (1886934395002866740172840496273538070047375333/1704569402656264759729675046812332851200000000000), (23545707037681274571606543593705612052795517/28020318947774215228433014468147937280000000000)]
    reserve := (37856739/100000000000) }

theorem quarter_017_027_valid : quarter_017_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_027]
  · intro i; fin_cases i <;> norm_num [quarter_017_027]
  · norm_num [quarter_017_027]
  · norm_num [quarter_017_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_027]

def quarter_017_028 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/128), (-1/160)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(20301553/100000000), (20201841/100000000), (6638157/50000000), (6638157/50000000), (468711/10000000), (1312959/25000000), (11502517/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(80873/25000000), 0, (4437731/25000000), 0, 0]] i.1) i.2
    mu := ![(3876363/50000000), (8383/10000000), (763531/12500000), (1/100000000), (3557583/100000000), (1778673/100000000), (9083/100000000)]
    alternative := .zero
    polynomial := [(-231129013233268692570786372263386060897609/8125571708503697264345174478906000000000000), (-3904465551167/454150000000), (-2565993878883110473675472597781098738065540609/4062785854251848632172587239453000000000000), (-3904465551167/454150000000), (-5131756628752987678658374409189934090070183609/8125571708503697264345174478906000000000000)]
    bernstein := [(15238560860326685411221776657444324472085612639/87247661873315562113617978105787779645440000000000), (121979555788994258776711913605921894518207119689/181765962236074087736704121053724540928000000000000), (9309229535206970944624910337217807982397549050837/10224335375779167435189606809272005427200000000000000), (1267988337265327595841599554492522730484281640557/1420046579969328810443000945732222976000000000000000), (3292853966421389699590439488311410058114797195591/5325174674884983039161253546495836160000000000000000)]
    reserve := (174658673/1000000000000) }

theorem quarter_017_028_valid : quarter_017_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_028]
  · intro i; fin_cases i <;> norm_num [quarter_017_028]
  · norm_num [quarter_017_028]
  · norm_num [quarter_017_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_028]

def quarter_017_029 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/160), (-7/1280)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(2030317/10000000), (5055019/25000000), (6647839/50000000), (6647839/50000000), (587069/12500000), (164489/3125000), (22925199/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(53729/20000000), 0, (2207497/12500000), 0, 0]] i.1) i.2
    mu := ![(7737883/100000000), (8419/12500000), (3057393/50000000), (1/100000000), (3562991/100000000), (1782489/100000000), (2263/50000000)]
    alternative := .zero
    polynomial := [(-25010726602029548494127118357662911710327253/636132463185189751836540525147346000000000000), (-6341772213307/452600000000), (-388729238326841332827240862790761138405094857253/318066231592594875918270262573673000000000000), (-6341772213307/452600000000), (-777433465927080636105987598463164613898479387253/636132463185189751836540525147346000000000000)]
    bernstein := [(215989491009433480442294258462094596508864298379147/416895771073045955763595198560564674560000000000000000), (2551765362116167289693789162128024643058277775697229/3335166168584367646108761588484517396480000000000000000), (71063093523440188285461598518147066611016388473632209/80043988046024823506610278123628417515520000000000000000), (189152838955306538065015051934959544512938673385900221/213450634789399529350960741663009113374720000000000000000), (1298136604575270263862003866985737436722370643711435947/1707605078315196234807685933304072906997760000000000000000)]
    reserve := (259044953/500000000000) }

theorem quarter_017_029_valid : quarter_017_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_029]
  · intro i; fin_cases i <;> norm_num [quarter_017_029]
  · norm_num [quarter_017_029]
  · norm_num [quarter_017_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_029]

def quarter_017_030 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/1280), (-3/640)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(2030423/10000000), (10116107/50000000), (13308549/100000000), (13308549/100000000), (188113/4000000), (658937/12500000), (2859017/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(232289/100000000), 0, (17599461/100000000), 0, 0]] i.1) i.2
    mu := ![(1932007/25000000), (3681/6250000), (1223827/20000000), (1/100000000), (1783293/50000000), (27891/1562500), (1129/25000000)]
    alternative := .zero
    polynomial := [(-774190298809655916079854183469577505689/26329269457963166228349997104000000000000), (-686960369519/56450000000), (-16168168039578511061636210116162033438845689/13164634728981583114174998552000000000000), (-686960369519/56450000000), (-32335561888858212467356340378140597300185689/26329269457963166228349997104000000000000)]
    bernstein := [(29493530886426142707615266896019030186607865475911/70677094530952153577109316002109194240000000000000000), (23465865012752560118814038701935448621464135985219/35338547265476076788554658001054597120000000000000000), (41654853491328209945454621516012837435438929610253/53007820898214115182831987001581895680000000000000000), (6914734824105308921934618999506117733987788463179/8834636816369019197138664500263649280000000000000000), (2891627707548540957684713201201078040537857259991/4417318408184509598569332250131824640000000000000000)]
    reserve := (417299707/1000000000000) }

theorem quarter_017_030_valid : quarter_017_030.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_030]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_030]
  · intro i; fin_cases i <;> norm_num [quarter_017_030]
  · norm_num [quarter_017_030]
  · norm_num [quarter_017_030, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_030, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_030, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_030, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_030]

def quarter_017_031 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/640), (-1/256)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(5076319/25000000), (20244339/100000000), (1332139/10000000), (1332139/10000000), (117727/2500000), (5279321/100000000), (11409601/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(196099/100000000), 0, (8769519/50000000), 0, 0]] i.1) i.2
    mu := ![(7718207/100000000), (12609/25000000), (3061739/50000000), (1/100000000), (892543/25000000), (1787551/100000000), (901/20000000)]
    alternative := .zero
    polynomial := [(-718021513008649974151285484128094486436059/34266330596548665875776306976272080000000000), (-68488590991/6625000000), (-21199965598163060338187799961862582041401737099/17133165298274332937888153488136040000000000), (-68488590991/6625000000), (-42399213174813112026401448638241035988317038139/34266330596548665875776306976272080000000000)]
    bernstein := [(1822739810750284712564803586591630807095218283865941/5748936299457058219097282698232235609292800000000000000), (1296002704226821751693847093780149614102564674709447/2299574519782823287638913079292894243717120000000000000), (269735166020365227750166054351156701465112765741633/394212774819912563595242242164496156065792000000000000), (249833078867628686995600049177738566902036474879311/367931923165251726022226092686863078994739200000000000), (80640639590705789123574758886445427124367151897029/147172769266100690408890437074745231597895680000000000)]
    reserve := (3963211/12500000000) }

theorem quarter_017_031_valid : quarter_017_031.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_031]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_031]
  · intro i; fin_cases i <;> norm_num [quarter_017_031]
  · norm_num [quarter_017_031]
  · norm_num [quarter_017_031, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_031, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_031, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_031, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_031]

def quarter_017_032 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/256), (-1/320)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(5076577/25000000), (405129/2000000), (13334201/100000000), (13334201/100000000), (4715319/100000000), (42297/800000), (5691599/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(80037/50000000), 0, (17478709/100000000), 0, 0]] i.1) i.2
    mu := ![(7708417/100000000), (10493/25000000), (3063907/50000000), (1/100000000), (3573749/100000000), (223759/12500000), (899/20000000)]
    alternative := .zero
    polynomial := [(-17746111096829100731668395560680037473719/1272555310338199525230413109046450000000000), (-956603389701/112375000000), (-113719165812113417123217333319084820094821917/90896807881299966087886650646175000000000), (-956603389701/112375000000), (-1592050575258491010624310998071626801290033119/1272555310338199525230413109046450000000000)]
    bernstein := [(1187877476317637741211655905723485323106471622689/5465583440253697660387351167924184494899200000000000), (3167982784309986085871654884504193112189063771937/6831979300317122075484188959905230618624000000000000), (2133014395218947590050211510986309913923316673477/3659988910884172540437958371377802117120000000000000), (6134043895681921210097646335724062970141765338401/10674967656745503242944045249851922841600000000000000), (5860297371553226443901629108686230115705733403681/13343709570931879053680056562314903552000000000000000)]
    reserve := (108668863/500000000000) }

theorem quarter_017_032_valid : quarter_017_032.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_032]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_032]
  · intro i; fin_cases i <;> norm_num [quarter_017_032]
  · norm_num [quarter_017_032]
  · norm_num [quarter_017_032, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_032, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_032, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_032, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_032]

def quarter_017_033 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/320), (-3/1280)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(20307327/100000000), (20268547/100000000), (13346981/100000000), (13346981/100000000), (4721539/100000000), (2647453/50000000), (11356859/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(24843/20000000), 0, (2177309/12500000), 0, 0]] i.1) i.2
    mu := ![(7698661/100000000), (6701/20000000), (6132143/100000000), (1/100000000), (1788659/50000000), (896293/50000000), (1121/25000000)]
    alternative := .zero
    polynomial := [(-9523907869044706775553728162084639318720321/1137051808692426720199082297780642000000000000), (-1501576405433/224200000000), (-723967177171593626243076759143398996442456528321/568525904346213360099541148890321000000000000), (-1501576405433/224200000000), (-1447924830435318207779377964558635908245594336321/1137051808692426720199082297780642000000000000)]
    bernstein := [(1408158950339561793273314200639550056943756222162879/11922852373514700405594729194776344657920000000000000000), (17381229972146128889885476104259194457419386743858237/47691409494058801622378916779105378631680000000000000000), (275422962384966909570667701390962757967048075664100133/572296913928705619468547001349264543580160000000000000000), (357515822392312295727126214980035755714751153137565733/763062551904940825958062668465686058106880000000000000000), (995823095615706366787158663118428244376333196909522799/3052250207619763303832250673862744232427520000000000000000)]
    reserve := (59052939/500000000000) }

theorem quarter_017_033_valid : quarter_017_033.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_033]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_033]
  · intro i; fin_cases i <;> norm_num [quarter_017_033]
  · norm_num [quarter_017_033]
  · norm_num [quarter_017_033, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_033, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_033, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_033, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_033]

def quarter_017_034 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/1280), (-1/640)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(20308331/100000000), (20280631/100000000), (13359731/100000000), (13359731/100000000), (2363871/50000000), (1060533/20000000), (22661167/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(2213/2500000), 0, (17358329/100000000), 0, 0]] i.1) i.2
    mu := ![(961117/12500000), (6259/25000000), (1227293/20000000), (1/100000000), (1790439/50000000), (448773/25000000), (2237/50000000)]
    alternative := .zero
    polynomial := [(-719861510080823139235840933736333604359/170132427432586184136577418989500000000000), (-546859397257/111850000000), (-6977105882093876762687422111643214085274999/5316638357268318254268044343421875000000), (-546859397257/111850000000), (-223266668365493975582858271731649114395195609/170132427432586184136577418989500000000000)]
    bernstein := [(8763513109497152757610430195091854546806540374871/456695757382531815980021257457494917120000000000000000), (8668115926385154555865461575257369097446837886651/32621125527323701141430089818392494080000000000000000), (129732329276778962055421232919372035290974882921757/342521818036898861985015943093121187840000000000000000), (2922006516564570431469005646667262964001161528739/8155281381830925285357522454598123520000000000000000), (5832598812352201067660452291221231554347694071591/28543484836408238498751328591093432320000000000000000)]
    reserve := (2398619/125000000000) }

theorem quarter_017_034_valid : quarter_017_034.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_034]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_034]
  · intro i; fin_cases i <;> norm_num [quarter_017_034]
  · norm_num [quarter_017_034]
  · norm_num [quarter_017_034, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_034, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_034, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_034, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_034]

def quarter_017_035 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/640), (-3/2560)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(5077269/25000000), (10144843/50000000), (6684637/50000000), (6684637/50000000), (4732383/100000000), (530847/10000000), (22621837/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1933/3125000), 0, (17313283/100000000), 0, 0]] i.1) i.2
    mu := ![(60013/781250), (16761/100000000), (3069851/50000000), (1/100000000), (1791771/50000000), (1796967/100000000), (2233/100000000)]
    alternative := .zero
    polynomial := [(-21253694000436056734789310670693238200497/5262475634230285705970015367225600000000000), (-53211074541/7975000000), (-6677017892668969925764791865393762752617304497/2631237817115142852985007683612800000000000), (-53211074541/7975000000), (-13354014531643939415472848941476854811996408497/5262475634230285705970015367225600000000000)]
    bernstein := [(168942395794960819915166906867067662459430443169103/882896904102184970307714373392632119296000000000000000), (29987607852993329365921585956810205458309662102057/95448313956992969762996148474879148032000000000000000), (15784847892394564458072143883372789597098532557872981/42379051396904878574770289922846341726208000000000000000), (390447567727513715820938132293296690597353730786977/1066139657783770530182900375417518030848000000000000000), (1259957731742148727728944348469326972717793129026531/4264558631135082120731601501670072123392000000000000000)]
    reserve := (95675041/500000000000) }

theorem quarter_017_035_valid : quarter_017_035.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_035]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_035]
  · intro i; fin_cases i <;> norm_num [quarter_017_035]
  · norm_num [quarter_017_035]
  · norm_num [quarter_017_035, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_035, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_035, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_035, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_035]

def quarter_017_036 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/2560), (-1/1280)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(317337/1562500), (10147859/50000000), (6687813/50000000), (6687813/50000000), (295967/6250000), (5312333/100000000), (22595657/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(11033/25000000), 0, (17283281/100000000), 0, 0]] i.1) i.2
    mu := ![(307073/4000000), (12523/100000000), (3070929/50000000), (1/100000000), (896329/25000000), (359643/20000000), (2231/100000000)]
    alternative := .zero
    polynomial := [(-11585747018604090874010209767194858757/5861247123205708516223950463000000000000), (-27193775711/5577500000), (-7671343615798393179561262887786864526848757/2930623561602854258111975231500000000000), (-27193775711/5577500000), (-2191810806549966822147378823623423122691251/837321017600815502317707209000000000000)]
    bernstein := [(35786705373015634891622937823414925399079617587083/251738647079426007576905526505090580480000000000000000), (33374916949215666557056617763708010389006155929561/125869323539713003788452763252545290240000000000000000), (60715971177091649150366866876295378524900659967961/188803985309569505682679144878817935360000000000000000), (9800139515586866420305641687614849255546266299729/31467330884928250947113190813136322560000000000000000), (38073008994897283480610726963859239901599879419/162202736520248716222232942335754240000000000000000)]
    reserve := (142158169/1000000000000) }

theorem quarter_017_036_valid : quarter_017_036.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_036]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_036]
  · intro i; fin_cases i <;> norm_num [quarter_017_036]
  · norm_num [quarter_017_036]
  · norm_num [quarter_017_036, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_036, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_036, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_036, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_036]

def quarter_017_037 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/1280), (-1/2560)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(20310057/100000000), (20301747/100000000), (13381971/100000000), (13381971/100000000), (1184639/25000000), (531619/10000000), (5642377/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(26449/100000000), 0, (17253303/100000000), 0, 0]] i.1) i.2
    mu := ![(1534399/20000000), (259/3125000), (1536003/25000000), (1/100000000), (3587087/100000000), (1799461/100000000), (557/25000000)]
    alternative := .zero
    polynomial := [(-3078203183575674395392954083042327479/4976581136977109316875924097000000000000), (-171851375431/55700000000), (-27707408936593030327256805828959610380965541/9953162273954218633751848194000000000000), (-171851375431/55700000000), (-27707402780186663175908015043051444296310583/9953162273954218633751848194000000000000)]
    bernstein := [(2478651787418860004785518803856550609634118435017/26717816536508976020748743607991664640000000000000000), (427966743677449480920640165884833052791530561771/1979097521222887112648055082073456640000000000000000), (286443421726785783757268555460084231477978269351/1065162121056836253318886788358471680000000000000000), (1985442485483641118623818195819176439372720500971/7916390084891548450592220328293826560000000000000000), (69204627577578125587443675303835186311828169711817/427485064584143616331979897727866634240000000000000000)]
    reserve := (18554299/200000000000) }

theorem quarter_017_037_valid : quarter_017_037.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_037]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_037]
  · intro i; fin_cases i <;> norm_num [quarter_017_037]
  · norm_num [quarter_017_037]
  · norm_num [quarter_017_037, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_037, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_037, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_037, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_037]

def quarter_017_038 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/2560), 0⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(20310543/100000000), (20307773/100000000), (3347077/25000000), (3347077/25000000), (948327/20000000), (5320041/100000000), (22543391/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(4403/50000000), 0, (4305837/25000000), 0, 0]] i.1) i.2
    mu := ![(7667173/100000000), (407/10000000), (1229233/20000000), (1/100000000), (448607/12500000), (900353/50000000), (1113/50000000)]
    alternative := .zero
    polynomial := [(131137606930225813382858458808789753489/3448799164749714863794458526698000000000000), (-389389901/300000000), (-5684411831215397105707247288185912709431554511/1724399582374857431897229263349000000000000), (-389389901/300000000), (-11368823793568401141640307959230284227652862511/3448799164749714863794458526698000000000000)]
    bernstein := [(168312093337573990960656226792565974803493138043197/4003372871100578747384403740053041315840000000000000000), (241263900469144677468165004241724454822678912271/1446531213190638805207255257636352819200000000000000), (741227961439594516927221617448634413697861931/3568744769384799683899478431668633600000000000000), (12123488151530749022939540802223209719557/73574382181327250427615115236224000000000000), (131137606930225813382858458808789753489/3448799164749714863794458526698000000000000)]
    reserve := (7604827/200000000000) }

theorem quarter_017_038_valid : quarter_017_038.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_038]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_038]
  · intro i; fin_cases i <;> norm_num [quarter_017_038]
  · norm_num [quarter_017_038]
  · norm_num [quarter_017_038, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_038, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_038, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_038, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_038]

def quarter_017_039 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/2560)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(40627/200000), (20313501/100000000), (13393/100000), (13393/100000), (237181/5000000), (2661211/50000000), (22520957/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1587/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (17200831/100000000), 0, 0]] i.1) i.2
    mu := ![(7663463/100000000), (1003/50000000), (3074013/50000000), (1/100000000), (3590141/100000000), (112593/6250000), (1121/25000000)]
    alternative := .zero
    polynomial := [(880448161913301844942590158083151/32644612746041435975615481000000000000), (251541709919/200600000000), (-884674236110889930445146435220044687807683/277479208341352205792731588500000000000), (251541709919/200600000000), (-1769348487189398613416424234464122063028933/554958416682704411585463177000000000000)]
    bernstein := [(880448161913301844942590158083151/32644612746041435975615481000000000000), (21228917412898479679470830501850025777/142069354670772329365878573312000000000000), (2081812119740650784799769428003418613465917/10910926438715314895299474430361600000000000000), (140677917860977329032251502077560101611932977/931065722770373537732221818057523200000000000000), (722320188634332007201287197243800162254231473467/23835282502921562565944878542272593920000000000000000)]
    reserve := (26970703/1000000000000) }

theorem quarter_017_039_valid : quarter_017_039.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_039]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_039]
  · intro i; fin_cases i <;> norm_num [quarter_017_039]
  · norm_num [quarter_017_039]
  · norm_num [quarter_017_039, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_039, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_039, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_039, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_039]

def quarter_017_040 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/2560), (1/1280)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(20318923/100000000), (20318937/100000000), (3349013/25000000), (3349013/25000000), (4744513/100000000), (1064667/20000000), (5625547/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(23811/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (687429/4000000), 0, 0]] i.1) i.2
    mu := ![(7660861/100000000), (1003/50000000), (6149597/100000000), (1/100000000), (3590943/100000000), (1801811/100000000), (4527/50000000)]
    alternative := .zero
    polynomial := [(-850690918907782514474316194246500413917/1428333540765453205737442111809000000000000), (574092987163/200600000000), (-1869364434715604576318589827252126192410196417/714166770382726602868721055904500000000000), (574092987163/200600000000), (-3738728018740290244854665180188058138319978917/1428333540765453205737442111809000000000000)]
    bernstein := [(7541507484900438006724588589935676441783430237998683/61346458453675043252606734329128303984640000000000000000), (17128894757528250007794065054211149417829556933841/84499254068422924590367402657201520640000000000000000), (125752787437953650251233415950004577464007790633631/582403086585522562524747477808180101120000000000000000), (3434109645595346545623083081619613149711831570641/21124813517105731147591850664300380160000000000000000), (163478445917651236924834104282428416833448538875483/3834153653354690203287920895570518999040000000000000000)]
    reserve := (21318713/500000000000) }

theorem quarter_017_040_valid : quarter_017_040.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_040]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_040]
  · intro i; fin_cases i <;> norm_num [quarter_017_040]
  · norm_num [quarter_017_040]
  · norm_num [quarter_017_040, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_040, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_040, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_040, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_040]

def quarter_017_041 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/1280), (3/2560)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(1270271/6250000), (32519/160000), (209361/1562500), (209361/1562500), (2372703/50000000), (5324247/100000000), (22483429/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(2481/6250000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1073163/6250000), 0, 0]] i.1) i.2
    mu := ![(382913/5000000), (2007/100000000), (6151169/100000000), (1/100000000), (1795873/50000000), (1802133/100000000), (3407/25000000)]
    alternative := .zero
    polynomial := [(-594460558163873132505582547171033327619/321754568624846841585739798158500000000000), (149507479001/33450000000), (-879349149657174661006298780379416944751597299/361973889702952696783957272928312500000000), (149507479001/33450000000), (-7034787847112373813192197692792411018712829821/2895791117623621574271658183426500000000000)]
    bernstein := [(1255898805668024254272989941237861671364624469557379/7773330091400464936610504323442241699840000000000000000), (3534745574174442015512744987749738659732506522758537/15546660182800929873221008646884483399680000000000000000), (21583262381027388084083491399739073121038912031598033/93279961096805579239326051881306900398080000000000000000), (3598921808089671642646869211689059552763543810707611/20728880243734573164294678195845977866240000000000000000), (747277199337658229613679693179222430578772634080411/13819253495823048776196452130563985244160000000000000000)]
    reserve := (54075077/1000000000000) }

theorem quarter_017_041_valid : quarter_017_041.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_041]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_041]
  · intro i; fin_cases i <;> norm_num [quarter_017_041]
  · norm_num [quarter_017_041]
  · norm_num [quarter_017_041, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_041, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_041, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_041, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_041]

def quarter_017_042 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/2560), (1/640)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(20329739/100000000), (4065963/20000000), (2680431/20000000), (2680431/20000000), (2373149/50000000), (2662579/50000000), (561617/2500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(55589/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (428887/2500000), 0, 0]] i.1) i.2
    mu := ![(7655663/100000000), (2007/100000000), (6152741/100000000), (1/100000000), (3592547/100000000), (360491/20000000), (9099/50000000)]
    alternative := .zero
    polynomial := [(-65953711245526516426695553941083756661497/17682709603832058592116598587201000000000000), (81352487437/13380000000), (-20660595508925090266684254175134875530690836497/8841354801916029296058299293600500000000000), (81352487437/13380000000), (-41321125064138935006852081654715809977625011497/17682709603832058592116598587201000000000000)]
    bernstein := [(141429075211387016761188730946461217470850296639643143/759466594531238079294965943507880991784960000000000000000), (46542710641701504929959146245188510024974423809028781/189866648632809519823741485876970247946240000000000000000), (34833542120378762113594268128674597632433483850231981/142399986474607139867806114407727685959680000000000000000), (2191455723162174124260349396964826461896562218687109/11866665539550594988983842867310640496640000000000000000), (193724886766047602167404170429225539924136529126103/2966666384887648747245960716827660124160000000000000000)]
    reserve := (65300529/1000000000000) }

theorem quarter_017_042_valid : quarter_017_042.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_042]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_042]
  · intro i; fin_cases i <;> norm_num [quarter_017_042]
  · norm_num [quarter_017_042]
  · norm_num [quarter_017_042, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_042, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_042, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_042, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_042]

def quarter_017_043 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/640), (1/512)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(5083783/25000000), (10167629/50000000), (13405207/100000000), (13405207/100000000), (4747189/100000000), (1331517/25000000), (1122297/5000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(71491/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (17140341/100000000), 0, 0]] i.1) i.2
    mu := ![(7653067/100000000), (251/12500000), (6154313/100000000), (1/100000000), (71867/2000000), (225347/12500000), (22761/100000000)]
    alternative := .zero
    polynomial := [(-377662902247313498238451842451589950787/60524185866185517322699012780125000000000), (771965412359/100400000000), (-8628214728223143776819987399656053784227989/3782761616636594832668688298757812500000), (771965412359/100400000000), (-46017019329556017705207186647551469652565679/20174728622061839107566337593375000000000)]
    bernstein := [(2085436150389497162785266438772717674798137472563/10154273395011415201946630403989176320000000000000000), (2113402444439963581879473216799588179456265637603/8123418716009132161557304323191341056000000000000000), (5009378267569398333198401330154644836140396443321/19496204918421917187737530375659218534400000000000000), (203502544197616313697061894009499367260186712487/1039797595649168916679334953368491655168000000000000), (12723594512193829944098705249752000383413621483/166367615303867026668693592538958664826880000000000)]
    reserve := (76478793/1000000000000) }

theorem quarter_017_043_valid : quarter_017_043.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_043]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_043]
  · intro i; fin_cases i <;> norm_num [quarter_017_043]
  · norm_num [quarter_017_043]
  · norm_num [quarter_017_043, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_043, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_043, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_043, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_043]

def quarter_017_044 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/512), (3/1280)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(4068103/20000000), (20340703/100000000), (6704129/50000000), (6704129/50000000), (4748079/100000000), (5326977/100000000), (22427209/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(87401/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2140649/12500000), 0, 0]] i.1) i.2
    mu := ![(3825237/50000000), (251/12500000), (3077943/50000000), (1/100000000), (3594151/100000000), (1803097/100000000), (27317/100000000)]
    alternative := .zero
    polynomial := [(-297512772722217698603204487677142892397759/31707142947290465554534893847446000000000000), (1867865454247/200800000000), (-35588267060309981357129725538076123453157244009/15853571473645232777267446923723000000000000), (1867865454247/200800000000), (-71176236607847240496560847871664569763422090259/31707142947290465554534893847446000000000000)]
    bernstein := [(1487131334841468986220181710793847184854522355337/6704302375788780375106061467845522861588480000000000), (533818450674048545192122987227607176403544129173/1948925109240924527647110891815558971392000000000000), (10985822549750545578288250055439077643219239341681663/40854342602462880410802562069683654937804800000000000000), (163743437803477491952367613294980688364878895253629/791750825629125589356638799800070832128000000000000000), (7458705512866982319588000694810349016642509699828221/85113213755131000855838670978507614453760000000000000000)]
    reserve := (21908189/250000000000) }

theorem quarter_017_044_valid : quarter_017_044.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_044]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_044]
  · intro i; fin_cases i <;> norm_num [quarter_017_044]
  · norm_num [quarter_017_044]
  · norm_num [quarter_017_044, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_044, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_044, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_044, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_044]

def quarter_017_045 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/1280), (7/2560)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(20345889/100000000), (20346151/100000000), (1341131/10000000), (1341131/10000000), (4748969/100000000), (1331971/25000000), (22408487/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(2583/2500000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (17110031/100000000), 0, 0]] i.1) i.2
    mu := ![(7647883/100000000), (2009/100000000), (307873/5000000), (1/100000000), (3594953/100000000), (901709/50000000), (6373/20000000)]
    alternative := .zero
    polynomial := [(-1285287979119717808860516139475418334873459/97722893002339918605718535799851000000000000), (545595227/50000000), (-108391651143094836591296332924623996451638613459/48861446501169959302859267899925500000000000), (545595227/50000000), (-216782016998210553464783805333108517484942353459/97722893002339918605718535799851000000000000)]
    bernstein := [(62100092876232834374767285208381357343290632586669021/262322893447223251179289393650853279170560000000000000000), (150507677913958657557287735246480124307345449761717849/524645786894446502358578787301706558341120000000000000000), (883302428240392075837127451581167211561072375956216943/3147874721366679014151472723810239350046720000000000000000), (457313155406813481886780273750787232949702592170911489/2098583147577786009434315149206826233364480000000000000000), (414729807776305942023600077126417098342928515763469741/4197166295155572018868630298413652466728960000000000000000)]
    reserve := (98811859/1000000000000) }

theorem quarter_017_045_valid : quarter_017_045.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_045]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_045]
  · intro i; fin_cases i <;> norm_num [quarter_017_045]
  · norm_num [quarter_017_045]
  · norm_num [quarter_017_045, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_045, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_045, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_045, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_045]

def quarter_017_046 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/2560), (1/320)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(5087813/25000000), (20351601/100000000), (13414361/100000000), (13414361/100000000), (2374929/50000000), (5328791/100000000), (895591/4000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(119247/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (854743/5000000), 0, 0]] i.1) i.2
    mu := ![(1529059/20000000), (2009/100000000), (3079517/50000000), (1/100000000), (719151/20000000), (1803739/100000000), (36407/100000000)]
    alternative := .zero
    polynomial := [(-13335706547236078404038373767795498567/759464047746952566021065365800000000000), (2516829480397/200900000000), (-835244432200564042911633971351726179085567/379732023873476283010532682900000000000), (2516829480397/200900000000), (-1670475528694580849744863904329684562672567/759464047746952566021065365800000000000)]
    bernstein := [(8177190055036539408207214095627349657116782629033/32618732475609437547237565931892768768000000000000000), (406948433907599245880959321131197072458506159173/1359113853150393231134898580495532032000000000000000), (63828474539485755829476767777751714631765943293/218429012113456055003822986151067648000000000000000), (4864618361498486500584801762925721972837166677/21236153955474894236482790320242688000000000000000), (875917957833233236856901633460391713931765833/7963557733303085338681046370091008000000000000000)]
    reserve := (109990783/1000000000000) }

theorem quarter_017_046_valid : quarter_017_046.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_046]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_046]
  · intro i; fin_cases i <;> norm_num [quarter_017_046]
  · norm_num [quarter_017_046]
  · norm_num [quarter_017_046, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_046, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_046, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_046, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_046]

def quarter_017_047 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/320), (9/2560)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(4071321/20000000), (10178527/50000000), (3354353/25000000), (3354353/25000000), (4750747/100000000), (5329697/100000000), (87387/390625)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(67591/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8539839/50000000), 0, 0]] i.1) i.2
    mu := ![(7642709/100000000), (201/10000000), (6160609/100000000), (1/100000000), (3596557/100000000), (1804059/100000000), (2047/5000000)]
    alternative := .zero
    polynomial := [(-94645122574553167508611453063908205782187/4189877247716504613012340905644700000000000), (710459745817/50250000000), (-4575748263578422944744226474219112516288206687/2094938623858252306506170452822350000000000), (710459745817/50250000000), (-9151401882034271336320944336985161124370631187/4189877247716504613012340905644700000000000)]
    bernstein := [(892355549708872253163446684439009128281955586401/3379542096078139646995406444213305344000000000000000), (8425842027370225101402103485418898063750332239209/27036336768625117175963251553706442752000000000000000), (365978618733225459092053092566703240873733422510737/1205048153115862365557219212108058591232000000000000000), (5403415075292078789943427653347910553771643280757477/22494232191496097490401425292683760369664000000000000000), (21805900698781471260721171789207080899197588516007693/179953857531968779923211402341470082957312000000000000000)]
    reserve := (24234991/200000000000) }

theorem quarter_017_047_valid : quarter_017_047.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_047]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_047]
  · intro i; fin_cases i <;> norm_num [quarter_017_047]
  · norm_num [quarter_017_047]
  · norm_num [quarter_017_047, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_047, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_047, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_047, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_047]

def quarter_017_048 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/2560), (1/256)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(20361949/100000000), (2036251/10000000), (13420463/100000000), (13420463/100000000), (950327/20000000), (2665301/50000000), (22352379/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(75563/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8532243/50000000), 0, 0]] i.1) i.2
    mu := ![(61121/800000), (201/10000000), (770273/12500000), (1/100000000), (1798679/50000000), (1804379/100000000), (45467/100000000)]
    alternative := .zero
    polynomial := [(-3758624270076057624681748566664452462883/132990191758076387656356025462000000000000), (39589515623/2512500000), (-433470106983423110892192766455373132503538649/199485287637114581484534038193000000000000), (39589515623/2512500000), (-866928938094035993611511487665046271649688649/398970575274229162969068076386000000000000)]
    bernstein := [(1582011957449232019938703894777943742834388541779037/5711885242897068288538672158918332907520000000000000000), (554713464803124097446136599275752636356485487633439/1713565572869120486561601647675499872256000000000000000), (162039171787598692391161424498728501510066277119669/514069671860736145968480494302649961676800000000000000), (4308545328069585272225802608957798889001491214703/17135655728691204865616016476754998722560000000000000), (75628293586897745155476140375676060490089722173/571188524289706828853867215891833290752000000000000)]
    reserve := (66202567/500000000000) }

theorem quarter_017_048_valid : quarter_017_048.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_048]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_048]
  · intro i; fin_cases i <;> norm_num [quarter_017_048]
  · norm_num [quarter_017_048]
  · norm_num [quarter_017_048, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_048, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_048, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_048, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_048]

def quarter_017_049 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/256), (11/2560)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(20367283/100000000), (636499/3125000), (6711757/50000000), (6711757/50000000), (2376261/50000000), (1066301/20000000), (4466739/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(83539/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8524641/50000000), 0, 0]] i.1) i.2
    mu := ![(954693/12500000), (2011/100000000), (77047/1250000), (1/100000000), (44977/1250000), (902349/50000000), (9997/20000000)]
    alternative := .zero
    polynomial := [(-115211172378698466219263217029556150883/3334216179814373044138348264500000000000), (1746432739397/100550000000), (-3605827066273605596239579093823075596943383/1667108089907186522069174132250000000000), (1746432739397/100550000000), (-7211538921374832494012938924429121637735883/3334216179814373044138348264500000000000)]
    bernstein := [(4147334159467053946114338371069374079646405173/14320349450096787575318170295485857792000000000000), (1780129340670289472147283775179373239076757317/5303833129665476879747470479809576960000000000000), (1403298404764650446905598091622849172067333265703/4296104835029036272595451088645757337600000000000000), (139306186758164955076437649098140419298773442461/530383312966547687974747047980957696000000000000000), (20571620732069864257363812697161463023912765487397/143203494500967875753181702954858577920000000000000000)]
    reserve := (143653063/1000000000000) }

theorem quarter_017_049_valid : quarter_017_049.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_049]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_049]
  · intro i; fin_cases i <;> norm_num [quarter_017_049]
  · norm_num [quarter_017_049]
  · norm_num [quarter_017_049, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_049, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_049, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_049, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_049]

def quarter_017_050 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/2560), (3/640)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(20372607/100000000), (20373429/100000000), (3356641/25000000), (3356641/25000000), (18568/390625), (666551/12500000), (1115751/5000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(183039/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4258517/25000000), 0, 0]] i.1) i.2
    mu := ![(1526993/20000000), (2011/100000000), (770667/12500000), (1/100000000), (3598961/100000000), (902509/50000000), (1703/3125000)]
    alternative := .zero
    polynomial := [(-83571993822414884457679888123434267698399/2013936870516277714996342751358000000000000), (3818883081171/201100000000), (-2170638106870645683576815355908203883895293399/1006968435258138857498171375679000000000000), (3818883081171/201100000000), (-4341192641747468952269173031928284333522888399/2013936870516277714996342751358000000000000)]
    bernstein := [(26124842662512465414391071023105932302926095992601441/86497929950759994215629008766892695879680000000000000000), (7514250841082875920255376392581855270559338093297993/21624482487689998553907252191723173969920000000000000000), (5483877368769956928427220862000690331788765287773267/16218361865767498915430439143792380477440000000000000000), (370247612394740932566107213948609109566600438887897/1351530155480624909619203261982698373120000000000000000), (52353435257952986677649914749424068474797668452481/337882538870156227404800815495674593280000000000000000)]
    reserve := (77472833/500000000000) }

theorem quarter_017_050_valid : quarter_017_050.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_050]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_050]
  · intro i; fin_cases i <;> norm_num [quarter_017_050]
  · norm_num [quarter_017_050]
  · norm_num [quarter_017_050, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_050, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_050, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_050, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_050]

def quarter_017_051 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/640), (13/2560)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(20377921/100000000), (5094723/25000000), (2685923/20000000), (2685923/20000000), (2377147/50000000), (5333309/100000000), (11148177/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(6219/3125000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4254711/25000000), 0, 0]] i.1) i.2
    mu := ![(1908097/25000000), (503/25000000), (6166913/100000000), (1/100000000), (3599763/100000000), (1805337/100000000), (58999/100000000)]
    alternative := .zero
    polynomial := [(-18553317600103089546601155663631453263631001/378235116391294275886210594149004500000000000), (259080191727/12575000000), (-406334668798486845236456795043456305207687858501/189117558195647137943105297074502250000000000), (259080191727/12575000000), (-812650784279373587383366988931248978962112086001/378235116391294275886210594149004500000000000)]
    bernstein := [(19944563749110099182707345608839869387168445026301119/63457322464818845861065465595261846814720000000000000000), (91188449013460557677864525378494331235567816911253649/253829289859275383444261862381047387258880000000000000000), (1064749537436223199987759019217699452518563516764902237/3045951478311304601331142348572568647106560000000000000000), (1158403485921784559396306552763224206675760350445647409/4061268637748406135108189798096758196142080000000000000000), (2700904391812343646119266866909758128159393311089248639/16245074550993624540432759192387032784568320000000000000000)]
    reserve := (33251979/200000000000) }

theorem quarter_017_051_valid : quarter_017_051.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_051]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_051]
  · intro i; fin_cases i <;> norm_num [quarter_017_051]
  · norm_num [quarter_017_051]
  · norm_num [quarter_017_051, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_051, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_051, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_051, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_051]

def quarter_017_052 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/2560), (7/1280)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(815329/4000000), (10192179/50000000), (2686533/20000000), (2686533/20000000), (4755179/100000000), (533421/10000000), (11138849/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(42997/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2125451/12500000), 0, 0]] i.1) i.2
    mu := ![(3814907/50000000), (2013/100000000), (6168491/100000000), (1/100000000), (900141/25000000), (361131/20000000), (12699/20000000)]
    alternative := .zero
    polynomial := [(-1265309359701375236396970168673310549/22106094906103763610291072375000000000), (745336869463/33550000000), (-71045672850656143632530359390826125141897/33159142359155645415436608562500000000), (745336869463/33550000000), (-142087549773233183139351527871146230352147/66318284718311290830873217125000000000)]
    bernstein := [(84531439404503484318242030107127154835326130903/258940785447239605878313758794711040000000000000000), (528323398731507422235932163788037919616968321687/1424174319959817832330725673370910720000000000000000), (771184967988067185845751149662875398223946405679/2136261479939726748496088510056366080000000000000000), (105580551098917624447515821815288151928668269327/356043579989954458082681418342727680000000000000000), (31614944098487360794256808785037153657921384653/178021789994977229041340709171363840000000000000000)]
    reserve := (35518061/200000000000) }

theorem quarter_017_052_valid : quarter_017_052.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_052]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_052]
  · intro i; fin_cases i <;> norm_num [quarter_017_052]
  · norm_num [quarter_017_052]
  · norm_num [quarter_017_052, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_052, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_052, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_052, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_052]

def quarter_017_053 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/1280), (3/512)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(20388519/100000000), (20389827/100000000), (3358929/25000000), (3358929/25000000), (4756063/100000000), (5335109/100000000), (22259051/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(230971/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (16988363/100000000), 0, 0]] i.1) i.2
    mu := ![(7627241/100000000), (2013/100000000), (6170069/100000000), (1/100000000), (720273/20000000), (902987/50000000), (67983/100000000)]
    alternative := .zero
    polynomial := [(-62389126406190467914049160614758032374743/944040866353372840704694221993000000000000), (1599691223781/67100000000), (-1009364791979656271893338397820933999257899743/472020433176686420352347110996500000000000), (1599691223781/67100000000), (-672889064944302117772920915493751080161141581/314680288784457613568231407331000000000000)]
    bernstein := [(857835346470890202113387070394850104327628343054457/2534140404422026956325799548212561838080000000000000000), (129308408646167564491176764059027199733538773206911/337885387256270260843439939761674911744000000000000000), (453110074572258980968467395881304483261662911576883/1216387394122572939036383783142029682278400000000000000), (49941328123368572215310451562128651965641150045301/162184985883009725204851171085603957637120000000000000), (12259170875001230257058036302592740855859015835113/64873994353203890081940468434241583054848000000000000)]
    reserve := (94484477/500000000000) }

theorem quarter_017_053_valid : quarter_017_053.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_053]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_053]
  · intro i; fin_cases i <;> norm_num [quarter_017_053]
  · norm_num [quarter_017_053]
  · norm_num [quarter_017_053, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_053, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_053, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_053, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_053]

def quarter_017_054 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/512), (1/160)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(20393803/100000000), (20395299/100000000), (6719383/50000000), (6719383/50000000), (4756947/100000000), (5336007/100000000), (22240413/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(49393/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8486553/50000000), 0, 0]] i.1) i.2
    mu := ![(238271/3125000), (1007/50000000), (6171647/100000000), (1/100000000), (1801083/50000000), (451573/25000000), (4529/6250000)]
    alternative := .zero
    polynomial := [(-28914826548672126976993354943653331262683/382781452711636221228272284228000000000000), (5126509401099/201400000000), (-408399752338380986276016214084043795336078933/191390726355818110614136142114000000000000), (5126509401099/201400000000), (-116681512835744757203579347830449133905842169/54683064673090888746896040604000000000000)]
    bernstein := [(9219916696751884917594008065601485784925591265153/26304541134589569421191206581479625719808000000000000), (3241800919604731740736488292641642529885357434923/8220169104559240444122252056712383037440000000000000), (2959029455473968072229592852064426564276650444587/7706408535524287916364611303167859097600000000000000), (36617082290248873074219197301697700143520641813/114678698445301903517330525344759808000000000000000), (50263690842450843098813154134180388762203655217/250859652849097913944160524191662080000000000000000)]
    reserve := (200365783/1000000000000) }

theorem quarter_017_054_valid : quarter_017_054.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_054]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_054]
  · intro i; fin_cases i <;> norm_num [quarter_017_054]
  · norm_num [quarter_017_054]
  · norm_num [quarter_017_054, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_054, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_054, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_054, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_054]

def quarter_017_055 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/160), (17/2560)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(10199539/50000000), (20400773/100000000), (1680227/12500000), (1680227/12500000), (475783/10000000), (667113/12500000), (2777723/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(32871/12500000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (211973/1250000), 0, 0]] i.1) i.2
    mu := ![(952763/12500000), (1007/50000000), (3086613/50000000), (1/100000000), (3602967/100000000), (1806609/100000000), (76937/100000000)]
    alternative := .zero
    polynomial := [(-144040884945617684784201006968074963180307/1681464301191328904809007883871500000000000), (681782477527/25175000000), (-33801969159617601620184649645891299097005619/15862870765955933064235923432750000000000), (681782477527/25175000000), (-3582864690034520154054788661457509629319415307/1681464301191328904809007883871500000000000)]
    bernstein := [(399421809869130094349689953755357000010310946293/1101964444428749311055631406774026240000000000000000), (265183812223558559181903417983189529409792854303/653015967068888480625559352162385920000000000000000), (334738159823857074757005812822706140626756959895231/846308693321279470890724920402452152320000000000000000), (55295888842650265039325438820017831110269778759167/167172087569635451040143194153570795520000000000000000), (2185382774506855503246599779721873727630356015159779/10316905975726073549905979982048940523520000000000000000)]
    reserve := (211825403/1000000000000) }

theorem quarter_017_055_valid : quarter_017_055.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_055]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_055]
  · intro i; fin_cases i <;> norm_num [quarter_017_055]
  · norm_num [quarter_017_055]
  · norm_num [quarter_017_055, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_055, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_055, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_055, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_055]

def quarter_017_056 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(17/2560), (9/1280)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(20404343/100000000), (653/3200), (6722433/50000000), (6722433/50000000), (594839/12500000), (26689/500000), (4440633/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(278979/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8471281/50000000), 0, 0]] i.1) i.2
    mu := ![(7619539/100000000), (403/20000000), (3087403/50000000), (1/100000000), (450471/12500000), (1806927/100000000), (40701/50000000)]
    alternative := .zero
    polynomial := [(-3363534740604539849764940459203165746500149/34897722069236391257485991861463000000000000), (57823939737/2015000000), (-37119787583008128546776110567444283036240225149/17448861034618195628742995930731500000000000), (57823939737/2015000000), (-5710477817790434811823265861109950992825688473/2684440159172030096729691681651000000000000)]
    bernstein := [(561152895603456547705417425270389429606373237701426171/1498845749922677481439626502231057477140480000000000000000), (24083605453745040758334305009275376361007473647541359/57647913458564518516908711624271441428480000000000000000), (457579133999016982201878279118269841097323625438226977/1124134312442008111079719876673293107855360000000000000000), (64118448140057207475353169452281242504071766190619443/187355718740334685179953312778882184642560000000000000000), (1609131085766879045586408324608819946445906872610247/7205989182320564814613588953033930178560000000000000000)]
    reserve := (55826169/250000000000) }

theorem quarter_017_056_valid : quarter_017_056.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_056]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_056]
  · intro i; fin_cases i <;> norm_num [quarter_017_056]
  · norm_num [quarter_017_056]
  · norm_num [quarter_017_056, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_056, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_056, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_056, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_056]

def quarter_017_057 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/1280), (1/128)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(20412221/100000000), (2041447/10000000), (84059/625000), (84059/625000), (2380017/50000000), (2669571/50000000), (22175253/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(303011/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (16919627/100000000), 0, 0]] i.1) i.2
    mu := ![(475981/6250000), (403/10000000), (772147/12500000), (1/100000000), (3604969/100000000), (903701/50000000), (11277/12500000)]
    alternative := .zero
    polynomial := [(-123903812804325707186103084615497090737243/2176579431205443301460897062789200000000000), (127290830167/8060000000), (-38224699509964247197865532971937506134872403/35106119858152311313885436496600000000000), (127290830167/8060000000), (-182292881984998384658498226244269991020873211/167429187015803330881607466368400000000000)]
    bernstein := [(130576609354890166085846613853043906549094623713829/449439301642964463315231822476061179904000000000000000), (224755778180883315031492189772535291961808855127833/584271092135853802309801369218879533875200000000000000), (64514292764517503383750232840856124379840463502259/175281327640756140692940410765663860162560000000000000), (281248304843380036734492874229318953366125100661/1168542184271707604619602738437759067750400000000000), (59361519113578780417967867000215636714600553/23370843685434152092392054768755181355008000000000)]
    reserve := (2539981/1000000000000) }

theorem quarter_017_057_valid : quarter_017_057.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_057]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_057]
  · intro i; fin_cases i <;> norm_num [quarter_017_057]
  · norm_num [quarter_017_057]
  · norm_num [quarter_017_057, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_057, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_057, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_057, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_057]

def quarter_017_058 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/128), (11/1280)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(5105673/25000000), (127659/625000), (13455539/100000000), (13455539/100000000), (4761793/100000000), (5340927/100000000), (2213807/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(167541/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1688901/10000000), 0, 0]] i.1) i.2
    mu := ![(7610579/100000000), (63/1562500), (6180339/100000000), (1/100000000), (360657/10000000), (904017/50000000), (49549/50000000)]
    alternative := .zero
    polynomial := [(-515612628245112669852817749182932325839/7410724902543575090256080148000000000000), (348349141/20000000), (-4018018792885798389548738919029519707625839/3705362451271787545128040074000000000000), (348349141/20000000), (-8035521973143351666427625020309856482925839/7410724902543575090256080148000000000000)]
    bernstein := [(25171627449816943990216175561323664410121369/79572052740193605568925281252037099520000000000), (542602103312790770953485496026954212864751349/1326200879003226759482088020867284992000000000000), (233724143228002551347888301538590724390708222907/596790395551452041766939609390278246400000000000000), (174939582842454627324297553399155973045613752577/663100439501613379741044010433642496000000000000000), (511132596285282125641465543841888246830261492001/19893013185048401392231320313009274880000000000000000)]
    reserve := (6423519/250000000000) }

theorem quarter_017_058_valid : quarter_017_058.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_058]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_058]
  · intro i; fin_cases i <;> norm_num [quarter_017_058]
  · norm_num [quarter_017_058]
  · norm_num [quarter_017_058, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_058, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_058, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_058, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_058]

def quarter_017_059 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/1280), (3/320)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(20433123/100000000), (10218211/50000000), (13461637/100000000), (13461637/100000000), (95271/2000000), (5342707/100000000), (5525231/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(367187/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1053647/6250000), 0, 0]] i.1) i.2
    mu := ![(237671/3125000), (807/20000000), (386469/6250000), (1/100000000), (3608171/100000000), (904333/50000000), (107949/100000000)]
    alternative := .zero
    polynomial := [(-12034417021601054162207792258402891746471/144151812458806598231170529592000000000000), (3841171470797/201750000000), (-77879080609373413476642958497352142298322471/72075906229403299115585264796000000000000), (3841171470797/201750000000), (-155746126801725225899123709202445881704898471/144151812458806598231170529592000000000000)]
    bernstein := [(132252790125074780911576363245108206979765121057289/386954575106062304119930545247900139520000000000000000), (5990287212575892174757059766401480236634900440071/13819806253787939432854662330282147840000000000000000), (30125889037530630002518437720475264669924222468043/72553982832386682022486977233981276160000000000000000), (247951013205352662262220622154772597341400202359/863737890861746214553416395642634240000000000000000), (74058548438711529801944450446454695608109636649/1511541309008055875468478692374609920000000000000000)]
    reserve := (9799077/200000000000) }

theorem quarter_017_059_valid : quarter_017_059.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_059]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_059]
  · intro i; fin_cases i <;> norm_num [quarter_017_059]
  · norm_num [quarter_017_059]
  · norm_num [quarter_017_059, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_059, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_059, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_059, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_059]

def quarter_017_060 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/320), (13/1280)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(4088703/20000000), (4089483/20000000), (2693547/20000000), (2693547/20000000), (595663/12500000), (5344483/100000000), (11031907/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(15973/4000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4206913/25000000), 0, 0]] i.1) i.2
    mu := ![(3800187/50000000), (4037/100000000), (6186671/100000000), (1/100000000), (3609771/100000000), (361859/20000000), (116769/100000000)]
    alternative := .zero
    polynomial := [(-655958716494180497726871228304729298664199/6646751688202445585177844975940500000000000), (8343307229111/403700000000), (-39392387133031914018148345275090379954353768689/36557134285113450718478147367672750000000000), (8343307229111/403700000000), (-78777558720182392050821694966669407886422231189/73114268570226901436956294735345500000000000)]
    bernstein := [(281358102888843951182835862578221535848570696668891/766658672802942434011578837084096430080000000000000000), (1403829135393334456637792392489992143890446913572661/3066634691211769736046315348336385720320000000000000000), (16152978800252095137230820054611485940443443297241393/36799616294541236832555784180036628643840000000000000000), (15234919839115095111875904051099802651625123886793301/49066155059388315776741045573382171525120000000000000000), (14215901361365326612705043905747601321124221782102171/196264620237553263106964182293528686100480000000000000000)]
    reserve := (72432317/1000000000000) }

theorem quarter_017_060_valid : quarter_017_060.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_060]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_060]
  · intro i; fin_cases i <;> norm_num [quarter_017_060]
  · norm_num [quarter_017_060]
  · norm_num [quarter_017_060, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_060, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_060, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_060, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_060]

def quarter_017_061 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/1280), (7/640)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(5113467/25000000), (20458419/100000000), (1684229/12500000), (1684229/12500000), (953411/20000000), (2673127/50000000), (1101337/5000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(431497/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (16796913/100000000), 0, 0]] i.1) i.2
    mu := ![(1519057/20000000), (4039/100000000), (77373/1250000), (1/100000000), (3611371/100000000), (452481/25000000), (3139/2500000)]
    alternative := .zero
    polynomial := [(-1024483455118882975479805604292301025699/8895021483982408309161901159200000000000), (9005678428963/403900000000), (-683079734611029085212223361131941183155957/635358677427314879225850082800000000000), (9005678428963/403900000000), (-9562091801099288309995647250242884263157699/8895021483982408309161901159200000000000)]
    bernstein := [(9360974033947028403035693736500930838280022898061/23877391481826144704480639154967805952000000000000000), (274073800866034429660452415238872087949944320299/568509320995860588201919979880185856000000000000000), (8287418301426027903397001332582274566800655216543/17908043611369608528360479366225854464000000000000000), (332386978712858376162014982711398316438732784853/994891311742756029353359964790325248000000000000000), (143326155905070972813089356726148221133716585501/1492336967614134044030039947185487872000000000000000)]
    reserve := (12005177/125000000000) }

theorem quarter_017_061_valid : quarter_017_061.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_061]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_061]
  · intro i; fin_cases i <;> norm_num [quarter_017_061]
  · norm_num [quarter_017_061]
  · norm_num [quarter_017_061, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_061, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_061, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_061, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_061]

def quarter_017_062 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/640), (3/256)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(10232091/50000000), (4093887/20000000), (1684991/12500000), (1684991/12500000), (4768803/100000000), (267401/5000000), (2748713/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(463701/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4191533/25000000), 0, 0]] i.1) i.2
    mu := ![(1518041/20000000), (4041/100000000), (1548253/25000000), (1/100000000), (361297/10000000), (1810551/100000000), (134319/100000000)]
    alternative := .zero
    polynomial := [(-10482063829841681963533776936406982781409/78845519450387695677102384457875000000000), (1074379807407/44900000000), (-42303380030550696893127023843152183112860159/39422759725193847838551192228937500000000), (1074379807407/44900000000), (-84596277997271552104290513909367959242938909/78845519450387695677102384457875000000000)]
    bernstein := [(324491559829383653664157169025872381243132320723/778122535559620973010007622449889280000000000000000), (157629519652347226423218092078950082471366442047/311249014223848389204003048979955712000000000000000), (3090344397294204726035651035622995780846699996577/6349479890166507139761662199191096524800000000000000), (60585074630724470609898371136525214539142665259/169319463737773523726977658645095907328000000000000), (1622207889874912809299968303822076402073524171/13545557099021881898158212691607672586240000000000)]
    reserve := (119759407/1000000000000) }

theorem quarter_017_062_valid : quarter_017_062.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_062]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_062]
  · intro i; fin_cases i <;> norm_num [quarter_017_062]
  · norm_num [quarter_017_062]
  · norm_num [quarter_017_062, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_062, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_062, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_062, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_062]

def quarter_017_063 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/256), (1/80)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(20474457/100000000), (10240231/50000000), (1685753/12500000), (1685753/12500000), (1192637/25000000), (2674891/50000000), (343011/1562500)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(247969/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (16735311/100000000), 0, 0]] i.1) i.2
    mu := ![(1517027/20000000), (4043/100000000), (6196187/100000000), (1/100000000), (361457/10000000), (1811177/100000000), (143049/100000000)]
    alternative := .zero
    polynomial := [(-13194177739891636568508175457639458900959509/86804066627714340387110038662147000000000000), (103345489279/4043000000), (-1906472131589516153976181297053597719934437249869/1779483365868143977935755792574013500000000000), (103345489279/4043000000), (-293261792453207442373311827608725555542610396913/273766671672022150451654737319079000000000000)]
    bernstein := [(270218534184938532334263552380904619476190259786411/611425828814374482676273337451835811356999680000000000), (507145270288419670378889863589658412613265214921757/955352857522460129181677089768493455245312000000000000), (2287297676923696089921252650051403869335289763156113/4478216519636531855539111358289813071462400000000000000), (178050954372818252872176646083869231663514774150473/466480887462138734951990766488522194944000000000000000), (20937596436947352295420114305321362948094712276931/145775277331918354672497114527663185920000000000000000)]
    reserve := (35907317/250000000000) }

theorem quarter_017_063_valid : quarter_017_063.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_063]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_063]
  · intro i; fin_cases i <;> norm_num [quarter_017_063]
  · norm_num [quarter_017_063]
  · norm_num [quarter_017_063, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_063, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_063, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_063, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_063]

def quarter_017_064 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/80), (17/1280)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(5121173/25000000), (20491501/100000000), (13492119/100000000), (13492119/100000000), (4772289/100000000), (2675769/50000000), (1095787/5000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(528209/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (16704451/100000000), 0, 0]] i.1) i.2
    mu := ![(7580073/100000000), (809/20000000), (6199363/100000000), (1/100000000), (452021/12500000), (1811801/100000000), (37937/25000000)]
    alternative := .zero
    polynomial := [(-67853826588432882453670199649435386708492811/393713052871297923830201140863469000000000000), (11001093588309/404500000000), (-210622529843195371085004831220190013804807539811/196856526435648961915100570431734500000000000), (11001093588309/404500000000), (-421177205859802309287555992240730592222906586811/393713052871297923830201140863469000000000000)]
    bernstein := [(7528735675337633164741761436867346610439456312389/16126486645608362960085038729767690240000000000000000), (143285469525767584198215130153969581666192319901013/258023786329733807361360619676283043840000000000000000), (2208457760005383711694588497120451885807643840197221/4128380581275740917781769914820528701440000000000000000), (26800226187915298321658775087596185500634560833207157/66054089300411854684508318637128459223040000000000000000), (177208846972352824040005001389248733266613492245211269/1056865428806589674952133098194055347568640000000000000000)]
    reserve := (167673993/1000000000000) }

theorem quarter_017_064_valid : quarter_017_064.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_064]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_064]
  · intro i; fin_cases i <;> norm_num [quarter_017_064]
  · norm_num [quarter_017_064]
  · norm_num [quarter_017_064, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_064, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_064, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_064, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_064]

def quarter_017_065 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(17/1280), (9/640)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(20494889/100000000), (2562819/12500000), (6749107/50000000), (6749107/50000000), (1193507/25000000), (535329/10000000), (5469703/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(4379/781250), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (16673551/100000000), 0, 0]] i.1) i.2
    mu := ![(378751/5000000), (4047/100000000), (3101271/50000000), (1/100000000), (3617767/100000000), (1812423/100000000), (5013/3125000)]
    alternative := .zero
    polynomial := [(-2993498611334738395306459639985780290325663/15432260338631188586630001093528000000000000), (486208897123/16862500000), (-24739235394270485502847118851024500036714471989/23148390507946782879945001640292000000000000), (486208897123/16862500000), (-49469490292706966790508318323129042732557966989/46296781015893565759890003280584000000000000)]
    bernstein := [(61119343251213441987573202918124481178894977143418931/124276975233335325722220595404650619863040000000000000000), (36033285004297020643817556414686340546096520654991387/62138487616667662861110297702325309931520000000000000000), (52127327104258098387953560735106640178029660151770697/93207731425001494291665446553487964897280000000000000000), (2226188659670055575693445864099780295893818446496441/5178207301388971905092524808527109160960000000000000000), (496716287665270387894641145078618896716744691417457/2589103650694485952546262404263554580480000000000000000)]
    reserve := (38369749/200000000000) }

theorem quarter_017_065_valid : quarter_017_065.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_065]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_065]
  · intro i; fin_cases i <;> norm_num [quarter_017_065]
  · norm_num [quarter_017_065]
  · norm_num [quarter_017_065, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_065, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_065, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_065, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_065]

def quarter_017_066 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/640), (19/1280)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(20505047/100000000), (1282101/6250000), (3376077/25000000), (3376077/25000000), (4775763/100000000), (5355037/100000000), (21841921/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(37053/6250000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (16642611/100000000), 0, 0]] i.1) i.2
    mu := ![(946247/12500000), (4049/100000000), (1551431/25000000), (1/100000000), (723873/20000000), (362609/20000000), (84527/50000000)]
    alternative := .zero
    polynomial := [(-91683442392604542207816977165407092913039/422694479661131185626908597849125000000000), (6169166047313/202450000000), (-225657692948003075338084856268360843601038039/211347239830565592813454298924562500000000), (6169166047313/202450000000), (-451223702453613546133961895559556280109163039/422694479661131185626908597849125000000000)]
    bernstein := [(36647918654333738160141983391786115157928084008321/70916365872824047055987409583719055360000000000000000), (12249220504853443351954174456725808877189306627373/20261818820806870587424974166776872960000000000000000), (165577249444497219948924183297328923755307735602201/283665463491296188223949638334876221440000000000000000), (36815760481808646063332623223527131785328097559013/81047275283227482349699896667107491840000000000000000), (245286843707479947434363711457732996258263040087281/1134661853965184752895798553339504885760000000000000000)]
    reserve := (216176161/1000000000000) }

theorem quarter_017_066_valid : quarter_017_066.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_066]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_066]
  · intro i; fin_cases i <;> norm_num [quarter_017_066]
  · norm_num [quarter_017_066]
  · norm_num [quarter_017_066, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_066, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_066, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_066, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_066]

def quarter_017_067 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(19/1280), (1/64)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(10257583/50000000), (20524691/100000000), (13510401/100000000), (13510401/100000000), (955499/20000000), (5356779/100000000), (10902533/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(625217/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1038227/6250000), 0, 0]] i.1) i.2
    mu := ![(7564941/100000000), (4051/100000000), (1552227/25000000), (1/100000000), (1810481/50000000), (56677/3125000), (88831/50000000)]
    alternative := .zero
    polynomial := [(-331118199392548670477911913744650164187313/1373235555628195699590056575332000000000000), (13009050377679/405100000000), (-732525647751405585378183135316294798768327313/686617777814097849795028287666000000000000), (13009050377679/405100000000), (-1464720177303418622085888358718844947372467313/1373235555628195699590056575332000000000000)]
    bernstein := [(1997280982196952730557850283149850670400156030560127/3686251125704680790766958498650437713920000000000000000), (38664081752955420019486441672507870713158160521591/61437518761744679846115974977507295232000000000000000), (16817697253676370228100066635776154273064832146933/27646883442785105930752188739878282854400000000000000), (73533810421700004850040402954707971270570967007/153593796904361699615289937443768238080000000000000), (5544907320839219086400618796217008783973763983/23039069535654254942293490616565235712000000000000)]
    reserve := (240674099/1000000000000) }

theorem quarter_017_067_valid : quarter_017_067.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_067]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_067]
  · intro i; fin_cases i <;> norm_num [quarter_017_067]
  · norm_num [quarter_017_067]
  · norm_num [quarter_017_067, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_067, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_067, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_067, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_067]

def quarter_017_068 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/64), (21/1280)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(20525247/100000000), (20535779/100000000), (6758247/50000000), (6758247/50000000), (597403/12500000), (1071703/20000000), (21768247/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(328809/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3316123/20000000), 0, 0]] i.1) i.2
    mu := ![(1511983/20000000), (4053/100000000), (1242419/20000000), (1/100000000), (3622559/100000000), (1814283/100000000), (291/156250)]
    alternative := .zero
    polynomial := [(-13804988948371218001923140496675446689965601/51774099359017799137018400100576000000000000), (5907232869/175000000), (-3942788159155312807087720058158014599757350443/3698149954215557081215600007184000000000000), (5907232869/175000000), (-55185229239226008081226157673715528949912940601/51774099359017799137018400100576000000000000)]
    bernstein := [(492462694374595204345576634699484869996932149191/868625248151703163966371294461785276416000000000000), (1623630755428955224093288963601294566013805608789/2481786423290580468475346555605100789760000000000000), (659849199520953109510969982965533643884134922910061/1042350297782043796759645553354142331699200000000000000), (94544864249987964292208050910578281077925139779487/187810864465233116533269469072818438144000000000000000), (996557878219550945182600794364852074470401027147787/3756217289304662330665389381456368762880000000000000000)]
    reserve := (2653089/10000000000) }

theorem quarter_017_068_valid : quarter_017_068.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_068]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_068]
  · intro i; fin_cases i <;> norm_num [quarter_017_068]
  · norm_num [quarter_017_068]
  · norm_num [quarter_017_068, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_068, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_068, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_068, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_068]

def quarter_017_069 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(21/1280), (11/640)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(20535289/100000000), (20546879/100000000), (6761293/50000000), (6761293/50000000), (4780949/100000000), (5360247/100000000), (2716433/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(172513/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8274779/50000000), 0, 0]] i.1) i.2
    mu := ![(3777449/50000000), (811/20000000), (1553821/25000000), (1/100000000), (906039/25000000), (1814899/100000000), (194787/100000000)]
    alternative := .zero
    polynomial := [(-33253408598402972147497529091802755133813/113317261532324896458978190272600000000000), (3588664280187/101375000000), (-60373372251299332306566437867606732373938413/56658630766162448229489095136300000000000), (3588664280187/101375000000), (-120713491094000261640985378206121661992743013/113317261532324896458978190272600000000000)]
    bernstein := [(180125886565821726728999350268277635556972326082347/304183707721008923211185957998801453056000000000000000), (103307361294701404676840911724572376661046143645877/152091853860504461605592978999400726528000000000000000), (150099244802708490755112171427927530449874408147521/228137780790756692408389468499101089792000000000000000), (20084680834904810241596236600863427927643685893237/38022963465126115401398244749850181632000000000000000), (5515544460849026148478031396695788855958594609067/19011481732563057700699122374925090816000000000000000)]
    reserve := (58023299/200000000000) }

theorem quarter_017_069_valid : quarter_017_069.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_069]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_069]
  · intro i; fin_cases i <;> norm_num [quarter_017_069]
  · norm_num [quarter_017_069]
  · norm_num [quarter_017_069, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_069, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_069, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_069, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_069]

def quarter_017_070 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/640), (23/1280)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(5136323/25000000), (2569749/12500000), (13528677/100000000), (13528677/100000000), (4782671/100000000), (5361973/100000000), (21694717/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(722519/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (258101/1562500), 0, 0]] i.1) i.2
    mu := ![(754989/10000000), (2029/50000000), (1554619/25000000), (1/100000000), (453219/12500000), (907757/50000000), (203303/100000000)]
    alternative := .zero
    polynomial := [(-1778830507713371424163415137596749187572239/5533063362710705273422834794394750000000000), (751480707251/20290000000), (-2945871172471910243912874662212363965565108489/2766531681355352636711417397197375000000000), (751480707251/20290000000), (-5889963514436107116401585909287131181942644739/5533063362710705273422834794394750000000000)]
    bernstein := [(44092036659355626103890881550967841489179460868577/71407230136833729141964583598366392320000000000000000), (100592609330684623558094429452960296092172905107461/142814460273667458283929167196732784640000000000000000), (245402789937328191270014887423054672038557959617137/359339609720840701488595969075650232320000000000000000), (4108065731991722675081906854191890278262113664738457/7426351934230707830764316694230104801280000000000000000), (275294701054806394126025037697754495176350238485453/873688462850671509501684316968247623680000000000000000)]
    reserve := (31509481/100000000000) }

theorem quarter_017_070_valid : quarter_017_070.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_070]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_070]
  · intro i; fin_cases i <;> norm_num [quarter_017_070]
  · norm_num [quarter_017_070]
  · norm_num [quarter_017_070, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_070, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_070, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_070, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_070]

def quarter_017_071 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(23/1280), (3/160)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(2569407/12500000), (10284559/50000000), (845923/6250000), (845923/6250000), (478439/10000000), (2681847/50000000), (10829003/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(377509/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (16487331/100000000), 0, 0]] i.1) i.2
    mu := ![(754489/10000000), (203/5000000), (622167/10000000), (1/100000000), (906837/25000000), (28377/1562500), (211789/100000000)]
    alternative := .zero
    polynomial := [(-15593989971578639755470556816818012461/44439643939119558027600546000000000000), (3926479335711/101500000000), (-165560899308734022574563130018170781635227/155538753786918453096601911000000000000), (3926479335711/101500000000), (-331012640687666994670837966138623837183227/311077507573836906193203822000000000000)]
    bernstein := [(76692009449534410254744966311813471392494394099/119291760852751947976574131513589760000000000000000), (76160667972113600895798000205297301232140733673/104380290746157954479502365074391040000000000000000), (27717671658257419487998254238382782182154183159/39142609029809232929813386902896640000000000000000), (943193864252341289796338490389828230149516833/1630942042908718038742224454287360000000000000000), (69359384687524154358996889002496410421797013/203867755363589754842778056785920000000000000000)]
    reserve := (85054383/250000000000) }

theorem quarter_017_071_valid : quarter_017_071.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_071]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_071]
  · intro i; fin_cases i <;> norm_num [quarter_017_071]
  · norm_num [quarter_017_071]
  · norm_num [quarter_017_071, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_071, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_071, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_071, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_071]

def quarter_017_072 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/160), (5/256)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(10282591/50000000), (643133/3125000), (6770429/50000000), (6770429/50000000), (957221/20000000), (536541/10000000), (21621331/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(787549/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (16456161/100000000), 0, 0]] i.1) i.2
    mu := ![(75399/1000000), (2031/50000000), (6224867/100000000), (1/100000000), (3628943/100000000), (90837/5000000), (44049/20000000)]
    alternative := .zero
    polynomial := [(-195636685614089795386013142982568397665693/512649814946713179305589162891000000000000), (4095902931397/101550000000), (-272762263381520857889598215556547167688004693/256324907473356589652794581445500000000000), (4095902931397/101550000000), (-545328890077427625983810417970111766978343693/512649814946713179305589162891000000000000)]
    bernstein := [(224578540407830602312624187036824590973495946467/335970182723477949189710913792245760000000000000000), (1475991595959453084567618525126651256219955687/1954735608572962613467408952973066240000000000000), (1632918560670900162640980524504042963865499327/2226273514509327566675564985266995200000000000000), (3020571485616910479744976161870506539307345623/5004123157946784290476566919611049574400000000000), (804765381991716265854214914592577746607848193347/2201814189496585087809689444628861812736000000000000)]
    reserve := (182750521/500000000000) }

theorem quarter_017_072_valid : quarter_017_072.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_072]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_072]
  · intro i; fin_cases i <;> norm_num [quarter_017_072]
  · norm_num [quarter_017_072]
  · norm_num [quarter_017_072, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_072, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_072, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_072, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_072]

def quarter_017_073 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(5/256), (13/640)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(2057507/10000000), (1286963/6250000), (13546947/100000000), (13546947/100000000), (4787817/100000000), (67089/1250000), (5396173/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(820113/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (16424953/100000000), 0, 0]] i.1) i.2
    mu := ![(3767459/50000000), (127/3125000), (6228067/100000000), (1/100000000), (1815269/50000000), (1817351/100000000), (228671/100000000)]
    alternative := .zero
    polynomial := [(-1487787710748605709174910530438163149934297069/3596801003128290717435444964027230400000000000), (213284022071/5080000000), (-1913302974743472222726231659392030382147063169069/1798400501564145358717722482013615200000000000), (213284022071/5080000000), (-3825118161776195839743288408253622601144192041069/3596801003128290717435444964027230400000000000)]
    bernstein := [(10722839289017733879039941015386965370250074863777251/15448142678656002323765613111704851021456998400000000000), (6029939016421988068134243405118215587657049377914271/7724071339328001161882806555852425510728499200000000000), (73281799448521357702894668394507888311871897211783443/96550891741600014523535081948155318884106240000000000000), (30369978872235716060343974541172848204305827002249359/48275445870800007261767540974077659442053120000000000000), (235926258126965819788362046494960119036117014390497091/603443073385000090772094262175970743025664000000000000000)]
    reserve := (97741721/250000000000) }

theorem quarter_017_073_valid : quarter_017_073.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_073]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_073]
  · intro i; fin_cases i <;> norm_num [quarter_017_073]
  · norm_num [quarter_017_073]
  · norm_num [quarter_017_073, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_073, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_073, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_073, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_073]

def quarter_017_074 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/640), (27/1280)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(20584919/100000000), (5150643/25000000), (3388259/25000000), (3388259/25000000), (191581/4000000), (214753/4000000), (2693511/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(85271/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4098427/25000000), 0, 0]] i.1) i.2
    mu := ![(1505989/20000000), (2033/50000000), (6231269/100000000), (1/100000000), (908033/25000000), (1817959/100000000), (118533/50000000)]
    alternative := .zero
    polynomial := [(-25281332300558253317490877190105541620875249/56560955237037297941720450570445500000000000), (2217906027717/50825000000), (-30082521535476028041314961526011728186597680249/28280477618518648970860225285222750000000000), (2217906027717/50825000000), (-60139761738651497829312432174833350831574485249/56560955237037297941720450570445500000000000)]
    bernstein := [(6831591917404510663075399264011649258916459136608111/9489353631781059476245994108376873697280000000000000000), (15304620267825105443106142857056263045377621060848969/18978707263562118952491988216753747394560000000000000000), (12764978830399935985173943662981647248019721400468379/16267463368767530530707418471503212052480000000000000000), (49706608847978563514536124818933892956191229049726329/75914829054248475809967952867014989578240000000000000000), (63256374033601557865240507313680752236495130158533391/151829658108496951619935905734029979156480000000000000000)]
    reserve := (416627257/1000000000000) }

theorem quarter_017_074_valid : quarter_017_074.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_074]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_074]
  · intro i; fin_cases i <;> norm_num [quarter_017_074]
  · norm_num [quarter_017_074]
  · norm_num [quarter_017_074, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_074, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_074, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_074, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_074]

def quarter_017_075 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(27/1280), (7/320)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(20594729/100000000), (16491/80000), (13559123/100000000), (13559123/100000000), (479123/10000000), (1342631/25000000), (134447/625000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(442669/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8181213/50000000), 0, 0]] i.1) i.2
    mu := ![(376249/5000000), (1017/25000000), (3117237/50000000), (1/100000000), (1816863/50000000), (1818567/100000000), (245431/100000000)]
    alternative := .zero
    polynomial := [(-1917094109388793444543151967872815654712279/3980528701659719898198831611097000000000000), (307085898737/6780000000), (-2116859261773314118252964000248215075599399779/1990264350829859949099415805548500000000000), (307085898737/6780000000), (-1410600476479079814353794949509519111848029093/1326842900553239966066277203699000000000000)]
    bernstein := [(7969685667097997854380958929934588606794431424092161/10685150371511148677052769421920378552320000000000000000), (741101396274092964032274343370863462927225800209367/890429197625929056421064118493364879360000000000000000), (1623879536549469024610836308334401258095885351125323/2003465694658340376947394266610070978560000000000000000), (113625803438918134753091750895359824434585096253181/166955474554861698078949522217505914880000000000000000), (6155257334683683191632152152335005053828808394107/13912956212905141506579126851458826240000000000000000)]
    reserve := (88482379/200000000000) }

theorem quarter_017_075_valid : quarter_017_075.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_075]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_075]
  · intro i; fin_cases i <;> norm_num [quarter_017_075]
  · norm_num [quarter_017_075]
  · norm_num [quarter_017_075, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_075, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_075, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_075, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_075]

def quarter_017_076 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/320), (3/128)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(20609373/100000000), (10315271/50000000), (6784127/50000000), (6784127/50000000), (239689/5000000), (5373063/100000000), (4291347/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(467171/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8157717/50000000), 0, 0]] i.1) i.2
    mu := ![(150351/2000000), (4071/50000000), (6239287/100000000), (1/100000000), (909029/25000000), (909737/50000000), (65517/25000000)]
    alternative := .zero
    polynomial := [(-971227822414130430448133058632585708753/3621684035083156354738322157250000000000), (2453172918263/101775000000), (-1957529960175425963236137701136375712344381/3621684035083156354738322157250000000000), (2453172918263/101775000000), (-489139683088252958201422392019435781658907/905421008770789088684580539312500000000)]
    bernstein := [(16858227070965888338546917197777427767601753679/28482082190785168183695681707704320000000000000000), (8829937766854568234117838122041656187522055851/11392832876314067273478272683081728000000000000000), (3364435568833900072090630596593600943950118647/4557133150525626909391309073232691200000000000000), (877838813980561999009862046417530318699966707/1822853260210250763756523629293076480000000000000), (1191687905306344020646671230090581197040757/243047101361366768500869817239076864000000000000)]
    reserve := (980623/200000000000) }

theorem quarter_017_076_valid : quarter_017_076.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_076]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_076]
  · intro i; fin_cases i <;> norm_num [quarter_017_076]
  · norm_num [quarter_017_076]
  · norm_num [quarter_017_076, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_076, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_076, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_076, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_076]

def quarter_017_077 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/128), (1/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(5157191/25000000), (10326489/50000000), (543217/4000000), (543217/4000000), (299823/6250000), (5376429/100000000), (5345953/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(62487/6250000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4063163/25000000), 0, 0]] i.1) i.2
    mu := ![(938459/12500000), (163/2000000), (6245713/100000000), (1/100000000), (3639301/100000000), (1820679/100000000), (69651/25000000)]
    alternative := .zero
    polynomial := [(-27658306465806283054102452549505415540977/90168488301885259845747016088100000000000), (1312327394761/50937500000), (-24344123298033910141125739505931180853807517/45084244150942629922873508044050000000000), (1312327394761/50937500000), (-5406732032178001555466375173256984032452673/10018720922431695538416335120900000000000)]
    bernstein := [(15636552235511126374059893434252504785557014247/24204419274147235386371589924248459673600000000000), (6266448608623826225348811108410736698252985037/7563881023171011058241121851327643648000000000000), (5610640788054958003870700297847966599987911693/7091138459222822867101051735619665920000000000000), (131541281231502982817624976881204392100248823/246220085389681349552119851931238400000000000000), (13276340477883557505853374929387477186681143/230831330052826265205112361185536000000000000000)]
    reserve := (57515331/1000000000000) }

theorem quarter_017_077_valid : quarter_017_077.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_077]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_077]
  · intro i; fin_cases i <;> norm_num [quarter_017_077]
  · norm_num [quarter_017_077]
  · norm_num [quarter_017_077, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_077, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_077, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_077, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_077]

def quarter_017_078 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (17/640)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(20648003/100000000), (2067547/10000000), (849537/6250000), (849537/6250000), (4800541/100000000), (5379771/100000000), (2131103/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1065371/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (16189727/100000000), 0, 0]] i.1) i.2
    mu := ![(7497829/100000000), (4079/50000000), (6252151/100000000), (1/100000000), (910621/25000000), (455469/25000000), (14751/5000000)]
    alternative := .zero
    polynomial := [(-50591282252642152192383979385182958744281/145397391403327697588960795366500000000000), (447495138297/16316000000), (-353037999207280734347181306227655055615758529/654288261314974639150323579149250000000000), (447495138297/16316000000), (-705620676874287689324631156640843464602818529/1308576522629949278300647158298500000000000)]
    bernstein := [(2346777220243915083139741578377251756590648671/3349955897932670152449656725244160000000000000000), (47299101211170974115018616748715774166525163807/53599294366922722439194507603906560000000000000000), (2173564551804221275058815531821923155083557944157/2572766129612290677081336364987514880000000000000000), (8063375872370668603773110026609156406899259190623/13721419357932216944433793946600079360000000000000000), (24340382025204644535495077509432386619729850484191/219542709726915471110940703145601269760000000000000000)]
    reserve := (2217371/20000000000) }

theorem quarter_017_078_valid : quarter_017_078.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_078]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_078]
  · intro i; fin_cases i <;> norm_num [quarter_017_078]
  · norm_num [quarter_017_078]
  · norm_num [quarter_017_078, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_078, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_078, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_078, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_078]

def quarter_017_079 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(17/640), (9/320)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(20667089/100000000), (20698017/100000000), (13604757/100000000), (13604757/100000000), (4803899/100000000), (5383091/100000000), (2123839/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1131077/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8063331/50000000), 0, 0]] i.1) i.2
    mu := ![(7488021/100000000), (4083/50000000), (31293/500000), (1/100000000), (113927/3125000), (1823067/100000000), (155657/50000000)]
    alternative := .zero
    polynomial := [(-199491047748101745789340440237402575561203/509149473101736002630913452436000000000000), (7919305453263/272200000000), (-137291640260511706584227728141674015283451203/254574736550868001315456726218000000000000), (7919305453263/272200000000), (-274383789473275311422666115843110627991341203/509149473101736002630913452436000000000000)]
    bernstein := [(64539194695658768622380641838357485016571974897837/85421106865140148911154032688244981760000000000000000), (2106432198336538330334854115914225610593331990471/2247923864872109181872474544427499520000000000000000), (57604539848248950987147518197713594796094171090519/64065830148855111683365524516183736320000000000000000), (360669664741355284631489339404725996083716775959/561980966218027295468118636106874880000000000000000), (880566402778624341998195868178350745820807960717/5338819179071259306947127043015311360000000000000000)]
    reserve := (164936547/1000000000000) }

theorem quarter_017_079_valid : quarter_017_079.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_079]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_079]
  · intro i; fin_cases i <;> norm_num [quarter_017_079]
  · norm_num [quarter_017_079]
  · norm_num [quarter_017_079, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_079, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_079, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_079, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_079]

def quarter_017_080 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/320), (19/640)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(2585753/12500000), (10360311/50000000), (6808459/50000000), (6808459/50000000), (4807241/100000000), (2693193/50000000), (2116589/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1196911/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8031729/50000000), 0, 0]] i.1) i.2
    mu := ![(3739123/50000000), (327/4000000), (6265061/100000000), (1/100000000), (3648843/100000000), (1824251/100000000), (5117/1562500)]
    alternative := .zero
    polynomial := [(-872033537223798352811732385524959677131/1989681283347885912713106578400000000000), (4191133783357/136250000000), (-9116647089703954547055786474625520166118567/16912290908457030258061405916400000000000), (4191133783357/136250000000), (-2602638515610729217444824785528159431103701/4832083116702008645160401690400000000000)]
    bernstein := [(287663796058280107758114604675180368333605220173/354676447032524779197539935403900928000000000000000), (54143058909522633572627016927753834807420201211/54565607235773042953467682369830912000000000000000), (580124956515703861975840017331362941375285659577/608016766341471050052925603549544448000000000000000), (21721558689768996657356257905478952997072971813/31180346991870310259124389925617664000000000000000), (1247170712231737862886798038001563754286228998653/5674823152520396467160638966462414848000000000000000)]
    reserve := (54943153/250000000000) }

theorem quarter_017_080_valid : quarter_017_080.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_080]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_080]
  · intro i; fin_cases i <;> norm_num [quarter_017_080]
  · norm_num [quarter_017_080]
  · norm_num [quarter_017_080, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_080, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_080, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_080, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_080]

def quarter_017_081 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(19/640), (1/32)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(20704807/100000000), (4148657/20000000), (3407269/25000000), (3407269/25000000), (601321/12500000), (2694829/50000000), (2109353/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(157859/12500000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8000059/50000000), 0, 0]] i.1) i.2
    mu := ![(1493701/20000000), (8183/100000000), (3135767/50000000), (1/100000000), (182601/5000000), (1825427/100000000), (171771/50000000)]
    alternative := .zero
    polynomial := [(-356577309243408135610552536041077607484177613/731503181112458797395608049196479000000000000), (53082661053/1636600000), (-197125272808924157664821203484513642939758152613/365751590556229398697804024598239500000000000), (53082661053/1636600000), (-393893968308604907194031854432986208272032127613/731503181112458797395608049196479000000000000)]
    bernstein := [(106421275643397603231447528334236522625165085617640627/122725868742108415350063536927079546224640000000000000000), (2143946475437686132346228076150571924212287999315531/2045431145701806922501058948784659103744000000000000000), (929551423457420482202690529985246331228108073990449/920444015565813115125476526953096596684800000000000000), (153879652730333807483609687029999539037562563211/204543114570180692250105894878465910374400000000000), (337955123545435121252508407938481349072394547/1227258687421084153500635369270795462246400000000)]
    reserve := (275373991/1000000000000) }

theorem quarter_017_081_valid : quarter_017_081.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_081]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_081]
  · intro i; fin_cases i <;> norm_num [quarter_017_081]
  · norm_num [quarter_017_081]
  · norm_num [quarter_017_081, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_081, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_081, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_081, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_081]

def quarter_017_082 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/32), (21/640)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(20723439/100000000), (20766007/100000000), (1364123/10000000), (1364123/10000000), (4813879/100000000), (674113/12500000), (2102131/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1328959/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3984161/25000000), 0, 0]] i.1) i.2
    mu := ![(7458797/100000000), (8191/100000000), (6278019/100000000), (1/100000000), (1827597/50000000), (456649/25000000), (14379/4000000)]
    alternative := .zero
    polynomial := [(-275815555292907445573539513073705439714826767/511419709071742642073353340789559000000000000), (27941542997133/819100000000), (-137811490323903774353558949094425905890085207767/255709854535871321036676670394779500000000000), (27941542997133/819100000000), (-91782388364171547087181452891926035446818529589/170473236357247547357784446929853000000000000)]
    bernstein := [(792687061644281420149455633711734509115556593/858019892575378580247533684274804188774400000000), (157986372676294950210226799915743090956321623871/143003315429229763374588947379134031462400000000000), (686254448725711098656737057668195626462575886729291/643514919431533935185650263206103141580800000000000000), (3469614961113861477110115215256869135927816984967053/4290099462876892901237668421374020943872000000000000000), (28463950820054685218377065968244321309674546948742673/85801989257537858024753368427480418877440000000000000000)]
    reserve := (331739987/1000000000000) }

theorem quarter_017_082_valid : quarter_017_082.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_082]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_082]
  · intro i; fin_cases i <;> norm_num [quarter_017_082]
  · norm_num [quarter_017_082]
  · norm_num [quarter_017_082, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_082, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_082, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_082, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_082]

def quarter_017_083 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(21/640), (11/320)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(20741921/100000000), (2078879/10000000), (13653381/100000000), (13653381/100000000), (2408587/50000000), (2698063/50000000), (5237307/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(348793/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (15873039/100000000), 0, 0]] i.1) i.2
    mu := ![(3724561/50000000), (8199/100000000), (1571129/25000000), (1/100000000), (3658367/100000000), (913879/50000000), (46911/12500000)]
    alternative := .zero
    polynomial := [(-156795026325074123489463559492483222427926883/264030210730540486967391549867618000000000000), (114638527979/3202734375), (-23717729722872202679855292619015319837223183961/44005035121756747827898591644603000000000000), (114638527979/3202734375), (-142149583310908141955642292154599435800911176883/264030210730540486967391549867618000000000000)]
    bernstein := [(43464962550117676257431471856061236022713483272399677/44296918759517955465971129887037985914880000000000000000), (25738938326826188065970963811955572377964289264436707/22148459379758977732985564943518992957440000000000000000), (1777743903632919890352234272744558393337931973411291/1582032812839926980927540353108499496960000000000000000), (4795043432840676809525589039986799891612042383301667/5537114844939744433246391235879748239360000000000000000), (1076675997217477105489860903486435928273613416529597/2768557422469872216623195617939874119680000000000000000)]
    reserve := (194447113/500000000000) }

theorem quarter_017_083_valid : quarter_017_083.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_083]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_083]
  · intro i; fin_cases i <;> norm_num [quarter_017_083]
  · norm_num [quarter_017_083]
  · norm_num [quarter_017_083, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_083, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_083, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_083, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_083]

def quarter_017_084 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/320), (23/640)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(5190063/25000000), (20811633/100000000), (1708191/12500000), (1708191/12500000), (1205113/25000000), (2699661/50000000), (10438643/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(182689/12500000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3161861/20000000), 0, 0]] i.1) i.2
    mu := ![(7439481/100000000), (8207/100000000), (251641/4000000), (1/100000000), (3661537/100000000), (114307/6250000), (19549/5000000)]
    alternative := .zero
    polynomial := [(-40923926154647499650628657032484236371528183/62854920227193434131863040057588500000000000), (61518262283/1641400000), (-16941715192518576835204256610535074121054131433/31427460113596717065931520028794250000000000), (61518262283/1641400000), (-33842506458882506170757884564037664005736734683/62854920227193434131863040057588500000000000)]
    bernstein := [(684957541964887921079208853469822228918190478539797/659081608321495823882524190914259189760000000000000000), (3099084324595014963381247346999221315230974021359/2539813519543336508217819618166702080000000000000000), (9346928556135939801989425650199721079612606569117159/7908979299857949886590290290971110277120000000000000000), (1624078822238784520735747248225464038322936752482443/1757550955523988863686731175771357839360000000000000000), (4712701233572652973804772281374716185850592660000197/10545305733143933182120387054628147036160000000000000000)]
    reserve := (111725097/250000000000) }

theorem quarter_017_084_valid : quarter_017_084.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_084]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_084]
  · intro i; fin_cases i <;> norm_num [quarter_017_084]
  · norm_num [quarter_017_084]
  · norm_num [quarter_017_084, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_084, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_084, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_084, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_084]

def quarter_017_085 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(23/640), (3/80)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(20778433/100000000), (10417269/50000000), (13677671/100000000), (13677671/100000000), (4823713/100000000), (1350623/25000000), (10402741/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(190997/12500000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3936361/25000000), 0, 0]] i.1) i.2
    mu := ![(464367/6250000), (1643/20000000), (6297547/100000000), (1/100000000), (57261/1562500), (915029/50000000), (406553/100000000)]
    alternative := .zero
    polynomial := [(-52804840667282929523769817056087925047469/74266451865856980339812161804480000000000), (8044127026087/205375000000), (-981123113509678980788796187353500904285398941/1819528070713496018325397964209760000000000), (8044127026087/205375000000), (-1959658789826661098030927653671253500243471901/3639056141426992036650795928419520000000000)]
    bernstein := [(670381269576168699498772318163270829774041522830659/610532309208471936291703198630148256563200000000000000), (97613630258530784529282112281477912801693729690399/76316538651058992036462899828768532070400000000000000), (35507493756122498674693593254423026536341687017217/28618701994147122013673587435788199526400000000000000), (1172092728782215359210565571540368287800540416679/1192445916422796750569732809824508313600000000000000), (75375890332110303730374901822484268894147563219/149055739552849593821216601228063539200000000000000)]
    reserve := (126422321/250000000000) }

theorem quarter_017_085_valid : quarter_017_085.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_085]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_085]
  · intro i; fin_cases i <;> norm_num [quarter_017_085]
  · norm_num [quarter_017_085]
  · norm_num [quarter_017_085, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_085, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_085, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_085, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_085]

def quarter_017_086 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/80), (13/320)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(494307/2000000), (2479089/10000000), (8097681/50000000), (8097681/50000000), (5650237/100000000), (6280433/100000000), (3086183/50000000)]
    cone := fun i => (![![0, 0, 0, (2317873/25000000), 0], ![(1933837/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2759381/50000000), (19547/100000000), (935299/12500000), (1/100000000), (4334143/100000000), (1067323/50000000), (65303/50000000)]
    alternative := .zero
    polynomial := [(-993104290567160705035028397108429123707220733/2078131685069024534122405982288731500000000000), (24091421410667/977350000000), (-329780212736006450846679964972579163791144268233/1039065842534512267061202991144365750000000000), (24091421410667/977350000000), (-658567321181445740988324901548049898458581315733/2078131685069024534122405982288731500000000000)]
    bernstein := [(71287394322577238443600671209066287788710838104027/85120273820427244917653749034546442240000000000000000), (520101285979344474874408589128959222510736839017717/340481095281708979670614996138185768960000000000000000), (365826442178107967387411624672726876429972857369259/215040691756868829265651576508327854080000000000000000), (7399389921239393636699887151606591259238665970523797/5447697524507343674729839938210972303360000000000000000), (10863459592351885096197765287278562517335355900460187/21790790098029374698919359752843889213440000000000000000)]
    reserve := (498534451/1000000000000) }

theorem quarter_017_086_valid : quarter_017_086.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_086]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_086]
  · intro i; fin_cases i <;> norm_num [quarter_017_086]
  · norm_num [quarter_017_086]
  · norm_num [quarter_017_086, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_086, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_086, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_086, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_086]

def quarter_017_087 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/320), (7/160)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(4985269/20000000), (2501523/10000000), (8105621/50000000), (8105621/50000000), (5554797/100000000), (3048669/50000000), (2991903/50000000)]
    cone := fun i => (![![0, 0, 0, (947127/10000000), 0], ![(210691/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5522771/100000000), (19719/100000000), (3766047/50000000), (1/100000000), (866011/20000000), (2084163/100000000), (13647/10000000)]
    alternative := .zero
    polynomial := [(-26256859825453585398741865792366379153736359/46769872808871949668751369876039875000000000), (735289271949/27387500000), (-1069053115207287787771824884083402424709662837/3340705200633710690625097848288562500000000), (735289271949/27387500000), (-14940486753076575443406806511375267566781543359/46769872808871949668751369876039875000000000)]
    bernstein := [(1015485342676317834667139377424710979567637750862801/490417661504357134958606364191383879680000000000000000), (75449559759133886383295650310008865092758672744571/27245425639130951942144798010632437760000000000000000), (154859273000650705625208926358648361733768655649309/52544749446895407316993539020505415680000000000000000), (17738541474529823778078394259883045565657582966291/6811356409782737985536199502658109440000000000000000), (53340542257669915089348856803214049853859942695841/30651103844022320934912897761961492480000000000000000)]
    reserve := (348049731/200000000000) }

theorem quarter_017_087_valid : quarter_017_087.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_087]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_087]
  · intro i; fin_cases i <;> norm_num [quarter_017_087]
  · norm_num [quarter_017_087]
  · norm_num [quarter_017_087, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_087, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_087, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_087, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_087]

def quarter_017_088 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/160), (1/20)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(1261821/5000000), (25347567/100000000), (1623169/10000000), (1623169/10000000), (676537/12500000), (1166133/20000000), (5709671/100000000)]
    cone := fun i => (![![0, 0, 0, (78107/800000), 0], ![(592781/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(691149/12500000), (9987/25000000), (7605487/100000000), (1/100000000), (4323419/100000000), (201019/10000000), (74393/50000000)]
    alternative := .zero
    polynomial := [(-60795818557608374263528495488775455236956067/174058669082703848910942661612734000000000000), (5046533694127/332900000000), (-14191413791340156708069601392434578021534231067/87029334541351924455471330806367000000000000), (5046533694127/332900000000), (-28322031764122705041875674289380380587831506067/174058669082703848910942661612734000000000000)]
    bernstein := [(284436530210424331454134579058669994652583353523533/114071089370040794422275382714521354240000000000000000), (18711306898905336742317539351196546780837582055673/4752962057085033100928140946438389760000000000000000), (23095123972101044020160381871527674082335065536551/5347082314220662238544158564743188480000000000000000), (270323995990638070953324782598887569966266065177/74265032141953642202002202288099840000000000000000), (52860198483952770131837379812971695132101320333/27849387053232615825750825858037440000000000000000)]
    reserve := (379614807/200000000000) }

theorem quarter_017_088_valid : quarter_017_088.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_088]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_088]
  · intro i; fin_cases i <;> norm_num [quarter_017_088]
  · norm_num [quarter_017_088]
  · norm_num [quarter_017_088, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_088, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_088, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_088, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_088]

def quarter_017_089 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (1/16)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(6458341/25000000), (25997359/100000000), (130089/800000), (130089/800000), (5130133/100000000), (5325171/100000000), (2595861/50000000)]
    cone := fun i => (![![0, 0, 0, (10320821/100000000), 0], ![(1457739/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2771653/50000000), (81881/100000000), (1937051/25000000), (1/100000000), (430849/10000000), (1868393/100000000), (169147/100000000)]
    alternative := .zero
    polynomial := [(-3815984428933105113717682289188722888336707951/14964447248511943962666932986810999250000000000), (38322467500383/4094050000000), (-629747845296983273282996547732550777236842925451/7482223624255971981333466493405499625000000000), (38322467500383/4094050000000), (-1255679706165033441452275413175912831585349142951/14964447248511943962666932986810999250000000000)]
    bernstein := [(7790994509083924046571259564776428086355215436249/2394311559761911034026709277889759880000000000000000), (12052105235554691996380161118658957051879411049329/1915449247809528827221367422311807904000000000000000), (32832838727233411984460238429710906799236630920811/4597078194742869185331281813548338969600000000000000), (7110775685306821830722964797731004339061929706353/1225887518598098449421675150279557058560000000000000), (2217959706088432383809040575329290819522688509401/980710014878478759537340120223645646848000000000000)]
    reserve := (2261585659/1000000000000) }

theorem quarter_017_089_valid : quarter_017_089.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_089]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_089]
  · intro i; fin_cases i <;> norm_num [quarter_017_089]
  · norm_num [quarter_017_089]
  · norm_num [quarter_017_089, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_089, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_089, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_089, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_089]

def quarter_017_090 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/16), (3/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(6175451/20000000), (31170527/100000000), (18976109/100000000), (18976109/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, (15438627/100000000), 0], ![(853157/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5620877/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5516893/100000000), (98029/100000000), (9220897/100000000), (1/100000000), (2466381/50000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-14909551218474656941262047815652573251/32798290074630275297762744000000000000), (26593353303739/1960580000000), (-1624996997507658039390775868985764373251/16399145037315137648881372000000000000), (26593353303739/1960580000000), (-3235084443796841421840289690155876173251/32798290074630275297762744000000000000)]
    bernstein := [(16987420142230743064573833977921826544701/2149468738330969721914179190784000000000000), (63297564064882564450748826324299562098999/5373671845827424304785447976960000000000000), (527192472808118895159518505908742747953839/40302538843705682285890859827200000000000000), (396398348360216960190694838469414918367663/33585449036421401904909049856000000000000000), (666402035472217987035988298235381373777869/83963622591053504762272624640000000000000000)]
    reserve := (1580615697/200000000000) }

theorem quarter_017_090_valid : quarter_017_090.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_090]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_090]
  · intro i; fin_cases i <;> norm_num [quarter_017_090]
  · norm_num [quarter_017_090]
  · norm_num [quarter_017_090, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_090, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_090, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_090, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_090]

def quarter_017_091 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(31110439/100000000), (31590493/100000000), (9324767/50000000), (9324767/50000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, (777761/5000000), 0], ![(1371583/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5524143/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5558557/100000000), (198241/100000000), (231737/2500000), (1/100000000), (4847871/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-599549353681305687603702802974985909/1650595722011239503816932000000000000), (43328983160419/4956025000000), (-41514288133354566559593598480320005909/825297861005619751908466000000000000), (43328983160419/4956025000000), (-82429026913027827431583494157665025909/1650595722011239503816932000000000000)]
    bernstein := [(49134219330083933363063868966820037282171/4225525048348773129771345920000000000000000), (20606659099274515103872139416365790904857/1056381262087193282442836480000000000000000), (17569139477386616483310262350484693644757/792285946565394961832127360000000000000000), (1294649392810873213347260890754368825973/66023828880449580152677280000000000000000), (194170619197683967275113949290949902291/16505957220112395038169320000000000000000)]
    reserve := (11627955997/1000000000000) }

theorem quarter_017_091_valid : quarter_017_091.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_091]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_091]
  · intro i; fin_cases i <;> norm_num [quarter_017_091]
  · norm_num [quarter_017_091]
  · norm_num [quarter_017_091, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_091, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_091, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_091, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_091]

def quarter_017_092 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![(3136297/10000000), (32167021/100000000), (3647001/20000000), (3647001/20000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, (3136297/20000000), 0], ![(1786781/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1350339/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5603677/100000000), (50231/25000000), (9343123/100000000), (1/100000000), (1185029/25000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-5697692356721269609966404736653613621/9349474856142127021762287000000000000), (57475421949401/5023100000000), (-240419495090690233461213336026237976121/4674737428071063510881143500000000000), (57475421949401/5023100000000), (-475141297824659197312460267315822338621/9349474856142127021762287000000000000)]
    bernstein := [(2512584321261062335705611701945553927179/93494748561421270217622870000000000000000), (872018488816796173666711023203969435533/24931932949712338724699432000000000000000), (6778396662397976345649213583213526008373/179509917237928838817835910400000000000000), (112311496776578053159960809684891771029/3191287417563179356761527296000000000000), (41694837945267277313387180615283029051/1531817960430326091245533102080000000000)]
    reserve := (2687406897/100000000000) }

theorem quarter_017_092_valid : quarter_017_092.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_092]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_092]
  · intro i; fin_cases i <;> norm_num [quarter_017_092]
  · norm_num [quarter_017_092]
  · norm_num [quarter_017_092, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_092, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_092, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_092, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_092]

def quarter_017_093 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![0, (24052909/50000000), (25947091/100000000), (25947091/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(15299657/100000000), 0, (46320569/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3842869/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (37341/12500000), (1726351/12500000), (1/100000000), (6744841/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-19323397952206206806506401421687/13913511122458788192000000000000), (6245880720059039/298728000000000), (-19935024423165401158859173698581/257657613378866448000000000000), (6245880720059039/298728000000000), (-1057167920898725455771888978301687/13913511122458788192000000000000)]
    bernstein := [(86820082477905141539128284403697/2279589662303647857377280000000000), (477639571687416856659334503922549/9498290259598532739072000000000000), (19413301708379899452140133984738433/356185884734944977715200000000000000), (15039436269207271120704353033892257/296821570612454148096000000000000000), (86120062679039797158710955717336953/2226161779593406110720000000000000000)]
    reserve := (38085837953/1000000000000) }

theorem quarter_017_093_valid : quarter_017_093.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_093]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_093]
  · intro i; fin_cases i <;> norm_num [quarter_017_093]
  · norm_num [quarter_017_093]
  · norm_num [quarter_017_093, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_093, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_093, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_093, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_093]

def quarter_017_094 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![0, (1982549/4000000), (25218137/100000000), (25218137/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(18044471/100000000), 0, (47013483/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (933727/12500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (152811/50000000), (14051637/100000000), (1/100000000), (819419/12500000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-625139814042680081708595436103/312798774425974459200000000000), (622274425023413/24449760000000), (-12549547052562777693096604336103/156399387212987229600000000000), (622274425023413/24449760000000), (-24473954291082875304484613236103/312798774425974459200000000000)]
    bernstein := [(3003586712626906203899791934854057/50047803908155913472000000000000000), (7283841903155484264787769919859733/100095607816311826944000000000000000), (46398944570004378111518383122152131/600573646897870961664000000000000000), (29386863577537489944830762933661613/400382431265247307776000000000000000), (48904431604918809002006520356686297/800764862530494615552000000000000000)]
    reserve := (60014355837/1000000000000) }

theorem quarter_017_094_valid : quarter_017_094.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_094]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_094]
  · intro i; fin_cases i <;> norm_num [quarter_017_094]
  · norm_num [quarter_017_094]
  · norm_num [quarter_017_094, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_094, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_094, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_094, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_094]

def quarter_017_095 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![0, (51016369/100000000), (3061477/12500000), (3061477/12500000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(20858957/100000000), 0, (23775553/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3627337/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (31201/10000000), (3574841/25000000), (1/100000000), (1591637/25000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-5844425779765097880364759698589/2130347820436501404000000000000), (9428540087644273/312010000000000), (-88661936957529995640089094126589/1065173910218250702000000000000), (9428540087644273/312010000000000), (-4182425564275485204873498257429/51959702937475644000000000000)]
    bernstein := [(448211650958356473246042547804860611/5453690420317443594240000000000000000), (21709817210914424735895718802798491/227237100846560149760000000000000000), (6412305550912543986176928734382023/63910434613095042120000000000000000), (171256002709965491507659652224667/1775289850363751170000000000000000), (27896279362434475416875057273459/332866846943203344375000000000000)]
    reserve := (41092509513/500000000000) }

theorem quarter_017_095_valid : quarter_017_095.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_095]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_095]
  · intro i; fin_cases i <;> norm_num [quarter_017_095]
  · norm_num [quarter_017_095]
  · norm_num [quarter_017_095, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_095, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_095, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_095, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_095]

def quarter_017_096 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![0, (10491247/20000000), (23771883/100000000), (23771883/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(23726859/100000000), 0, (5990433/12500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (440089/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (63567/20000000), (3638043/25000000), (1/100000000), (1544851/25000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-91522601557173648216339319/25203628781743720000000000), (124325274115107/3531500000000), (-3264751932096707703712357157/37805443172615580000000000), (124325274115107/3531500000000), (-6254936059521894462775696357/75610886345231160000000000)]
    bernstein := [(1235964657144135851506516267/11814200991442368750000000000), (2038276898290092061588482821/17184292351188900000000000000), (1858907054311770682932489481/15022030399714800000000000000), (87905614234093052487917022359/733196473650726400000000000000), (6897603499633330876582964208041/64521289681263923200000000000000)]
    reserve := (52308431947/500000000000) }

theorem quarter_017_096_valid : quarter_017_096.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_096]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_096]
  · intro i; fin_cases i <;> norm_num [quarter_017_096]
  · norm_num [quarter_017_096]
  · norm_num [quarter_017_096, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_096, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_096, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_096, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_096]

def quarter_017_097 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![0, (53874957/100000000), (23062521/100000000), (23062521/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(26630293/100000000), 0, (12030427/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3415653/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (161521/50000000), (14807977/100000000), (1/100000000), (5995009/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-200864227258375760836734089210903/43016574144090576459000000000000), (3262695357022683/80760500000000), (-1926999407788365499641526551020903/21508287072045288229500000000000), (3262695357022683/80760500000000), (-3653134588318355238446319012830903/43016574144090576459000000000000)]
    bernstein := [(14020982959092214274493725589850947817/110122429808871875735040000000000000000), (1563770987500650171985681649574523633/11012242980887187573504000000000000000), (487308409008303141296052765901727803/3303672894266156272051200000000000000), (15823194565932059746573544199209681/110122429808871875735040000000000000), (1435729986841308497677871769061033/11012242980887187573504000000000000)]
    reserve := (63660886267/500000000000) }

theorem quarter_017_097_valid : quarter_017_097.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_097]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_097]
  · intro i; fin_cases i <;> norm_num [quarter_017_097]
  · norm_num [quarter_017_097]
  · norm_num [quarter_017_097, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_097, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_097, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_097, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_097]

def quarter_017_098 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![0, (27631693/50000000), (22368307/100000000), (22368307/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(7387469/25000000), 0, (1203459/2500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3312837/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (163789/50000000), (15064439/100000000), (1/100000000), (5814551/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-6821417524347967874024727621943/1163250932392057899000000000000), (375002941283947/8189450000000), (-54055715801945626553488971021943/581625466196028949500000000000), (375002941283947/8189450000000), (-101290014079543285232953214421943/1163250932392057899000000000000)]
    bernstein := [(44759407462582567387258890378473/297792238692366822144000000000000), (8657442306486637931078644460907/52244252402169617920000000000000), (15331467355525430363857983420383123/89337671607710046643200000000000000), (876908666018130331728851099928291/5224425240216961792000000000000000), (459259768655299314698292903847522937/2977922386923668221440000000000000000)]
    reserve := (30060828757/200000000000) }

theorem quarter_017_098_valid : quarter_017_098.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_098]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_098]
  · intro i; fin_cases i <;> norm_num [quarter_017_098]
  · norm_num [quarter_017_098]
  · norm_num [quarter_017_098, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_098, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_098, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_098, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_098]

def quarter_017_099 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![0, (442279/781250), (338971/1562500), (338971/1562500), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1298597/4000000), 0, (2398379/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6425981/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2589/781250), (7659499/50000000), (1/100000000), (1127861/20000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1291930438926933224673566333977/178927865376346968000000000000), (2216300316389/43150000000), (-2874292381062509639517721844659/29821310896057828000000000000), (2216300316389/43150000000), (-15953823847448124612432764733977/178927865376346968000000000000)]
    bernstein := [(26500134273467877986152557777342781/152685111787816079360000000000000000), (21726798716428920603162804165877439/114513833840862059520000000000000000), (5612909641458511741010488900520347/28628458460215514880000000000000000), (1376795173841122553758957276487531/7157114615053878720000000000000000), (319268209929382399190706597219263/1789278653763469680000000000000000)]
    reserve := (173560696017/1000000000000) }

theorem quarter_017_099_valid : quarter_017_099.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_099]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_099]
  · intro i; fin_cases i <;> norm_num [quarter_017_099]
  · norm_num [quarter_017_099]
  · norm_num [quarter_017_099, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_099, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_099, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_099, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_099]

def quarter_017_100 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![0, (1447741/2500000), (1052259/5000000), (1052259/5000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(8838433/25000000), 0, (47605433/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6233753/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (167219/50000000), (7784457/50000000), (1/100000000), (5470609/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-33202198401267665860309670516121/3797942186856050958400000000000), (954740609211387/16721900000000), (-189736716665527990413233776596121/1898971093428025479200000000000), (954740609211387/16721900000000), (-346271234929788314966157882676121/3797942186856050958400000000000)]
    bernstein := [(7485000203682858547032473633646399/37979421868560509584000000000000000), (32517745513971879228719150998654029/151917687474242038336000000000000000), (402580883570592038237752837572242177/1823012249690904460032000000000000000), (40616543064055849603545113381076653/186975615352913277952000000000000000), (1973689211263731000126116028511471319/9722731998351490453504000000000000000)]
    reserve := (197080414483/1000000000000) }

theorem quarter_017_100_valid : quarter_017_100.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_100]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_100]
  · intro i; fin_cases i <;> norm_num [quarter_017_100]
  · norm_num [quarter_017_100]
  · norm_num [quarter_017_100, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_100, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_100, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_100, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_100]

def quarter_017_101 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![0, (462083/781250), (319167/1562500), (319167/1562500), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(19096959/50000000), 0, (11762537/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (121011/2000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (336677/100000000), (7905667/50000000), (1/100000000), (1061967/20000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-35740294053701733533061011971/3426171031895097640000000000), (82808532671399/1315144531250), (-177338108189709254314797255171/1713085515947548820000000000), (82808532671399/1315144531250), (-318935922325716775096533498371/3426171031895097640000000000)]
    bernstein := [(1937028073880658348488252040619469/8770997841651449958400000000000000), (1046562680635799224570887220343591/4385498920825724979200000000000000), (539207991622645946794906833734949/2192749460412862489600000000000000), (1102779576270763195532928775871/4549272739445772800000000000000), (124924920533752048260995743656829/548187365103215622400000000000000)]
    reserve := (27605583037/125000000000) }

theorem quarter_017_101_valid : quarter_017_101.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_101]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_101]
  · intro i; fin_cases i <;> norm_num [quarter_017_101]
  · norm_num [quarter_017_101]
  · norm_num [quarter_017_101, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_101, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_101, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_101, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_101]

def quarter_017_102 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 1, 0, 0, 0, 2, 1]
    lambda := ![0, (60312151/100000000), (4960981/25000000), (4960981/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(40962871/100000000), 0, (46302341/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5877931/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (84519/25000000), (16043363/100000000), (1/100000000), (5158347/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-91687146745926825344881620201299/7460862517136877609600000000000), (15539527813621643/225384000000000), (-399830260632341639650408442669299/3730431258568438804800000000000), (15539527813621643/225384000000000), (-78663708279861828217326140570811/828984724126319734400000000000)]
    bernstein := [(292259686510284861677971006880896301/1193738002741900417536000000000000000), (41936859269511776296985842504494923/159165067032253389004800000000000000), (155421557592774676173316340060198399/572994241316112200417280000000000000), (20465095249981495171559876748719113/76399232175481626722304000000000000), (7733781157205017625837313749564029/30559692870192650688921600000000000)]
    reserve := (24482732881/100000000000) }

theorem quarter_017_102_valid : quarter_017_102.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_017_102]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_017_102]
  · intro i; fin_cases i <;> norm_num [quarter_017_102]
  · norm_num [quarter_017_102]
  · norm_num [quarter_017_102, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_017_102, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_017_102, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_017_102, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_017_102]

def quarterTable017 : OwnerTable where
  mode := .quarter
  owners := ![0, 1, 0, 0, 0, 2, 1]
  rows := [quarter_017_000, quarter_017_001, quarter_017_002, quarter_017_003, quarter_017_004, quarter_017_005, quarter_017_006, quarter_017_007, quarter_017_008, quarter_017_009, quarter_017_010, quarter_017_011, quarter_017_012, quarter_017_013, quarter_017_014, quarter_017_015, quarter_017_016, quarter_017_017, quarter_017_018, quarter_017_019, quarter_017_020, quarter_017_021, quarter_017_022, quarter_017_023, quarter_017_024, quarter_017_025, quarter_017_026, quarter_017_027, quarter_017_028, quarter_017_029, quarter_017_030, quarter_017_031, quarter_017_032, quarter_017_033, quarter_017_034, quarter_017_035, quarter_017_036, quarter_017_037, quarter_017_038, quarter_017_039, quarter_017_040, quarter_017_041, quarter_017_042, quarter_017_043, quarter_017_044, quarter_017_045, quarter_017_046, quarter_017_047, quarter_017_048, quarter_017_049, quarter_017_050, quarter_017_051, quarter_017_052, quarter_017_053, quarter_017_054, quarter_017_055, quarter_017_056, quarter_017_057, quarter_017_058, quarter_017_059, quarter_017_060, quarter_017_061, quarter_017_062, quarter_017_063, quarter_017_064, quarter_017_065, quarter_017_066, quarter_017_067, quarter_017_068, quarter_017_069, quarter_017_070, quarter_017_071, quarter_017_072, quarter_017_073, quarter_017_074, quarter_017_075, quarter_017_076, quarter_017_077, quarter_017_078, quarter_017_079, quarter_017_080, quarter_017_081, quarter_017_082, quarter_017_083, quarter_017_084, quarter_017_085, quarter_017_086, quarter_017_087, quarter_017_088, quarter_017_089, quarter_017_090, quarter_017_091, quarter_017_092, quarter_017_093, quarter_017_094, quarter_017_095, quarter_017_096, quarter_017_097, quarter_017_098, quarter_017_099, quarter_017_100, quarter_017_101, quarter_017_102]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_017_000_valid
    · exact quarter_017_001_valid
    · exact quarter_017_002_valid
    · exact quarter_017_003_valid
    · exact quarter_017_004_valid
    · exact quarter_017_005_valid
    · exact quarter_017_006_valid
    · exact quarter_017_007_valid
    · exact quarter_017_008_valid
    · exact quarter_017_009_valid
    · exact quarter_017_010_valid
    · exact quarter_017_011_valid
    · exact quarter_017_012_valid
    · exact quarter_017_013_valid
    · exact quarter_017_014_valid
    · exact quarter_017_015_valid
    · exact quarter_017_016_valid
    · exact quarter_017_017_valid
    · exact quarter_017_018_valid
    · exact quarter_017_019_valid
    · exact quarter_017_020_valid
    · exact quarter_017_021_valid
    · exact quarter_017_022_valid
    · exact quarter_017_023_valid
    · exact quarter_017_024_valid
    · exact quarter_017_025_valid
    · exact quarter_017_026_valid
    · exact quarter_017_027_valid
    · exact quarter_017_028_valid
    · exact quarter_017_029_valid
    · exact quarter_017_030_valid
    · exact quarter_017_031_valid
    · exact quarter_017_032_valid
    · exact quarter_017_033_valid
    · exact quarter_017_034_valid
    · exact quarter_017_035_valid
    · exact quarter_017_036_valid
    · exact quarter_017_037_valid
    · exact quarter_017_038_valid
    · exact quarter_017_039_valid
    · exact quarter_017_040_valid
    · exact quarter_017_041_valid
    · exact quarter_017_042_valid
    · exact quarter_017_043_valid
    · exact quarter_017_044_valid
    · exact quarter_017_045_valid
    · exact quarter_017_046_valid
    · exact quarter_017_047_valid
    · exact quarter_017_048_valid
    · exact quarter_017_049_valid
    · exact quarter_017_050_valid
    · exact quarter_017_051_valid
    · exact quarter_017_052_valid
    · exact quarter_017_053_valid
    · exact quarter_017_054_valid
    · exact quarter_017_055_valid
    · exact quarter_017_056_valid
    · exact quarter_017_057_valid
    · exact quarter_017_058_valid
    · exact quarter_017_059_valid
    · exact quarter_017_060_valid
    · exact quarter_017_061_valid
    · exact quarter_017_062_valid
    · exact quarter_017_063_valid
    · exact quarter_017_064_valid
    · exact quarter_017_065_valid
    · exact quarter_017_066_valid
    · exact quarter_017_067_valid
    · exact quarter_017_068_valid
    · exact quarter_017_069_valid
    · exact quarter_017_070_valid
    · exact quarter_017_071_valid
    · exact quarter_017_072_valid
    · exact quarter_017_073_valid
    · exact quarter_017_074_valid
    · exact quarter_017_075_valid
    · exact quarter_017_076_valid
    · exact quarter_017_077_valid
    · exact quarter_017_078_valid
    · exact quarter_017_079_valid
    · exact quarter_017_080_valid
    · exact quarter_017_081_valid
    · exact quarter_017_082_valid
    · exact quarter_017_083_valid
    · exact quarter_017_084_valid
    · exact quarter_017_085_valid
    · exact quarter_017_086_valid
    · exact quarter_017_087_valid
    · exact quarter_017_088_valid
    · exact quarter_017_089_valid
    · exact quarter_017_090_valid
    · exact quarter_017_091_valid
    · exact quarter_017_092_valid
    · exact quarter_017_093_valid
    · exact quarter_017_094_valid
    · exact quarter_017_095_valid
    · exact quarter_017_096_valid
    · exact quarter_017_097_valid
    · exact quarter_017_098_valid
    · exact quarter_017_099_valid
    · exact quarter_017_100_valid
    · exact quarter_017_101_valid
    · exact quarter_017_102_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
