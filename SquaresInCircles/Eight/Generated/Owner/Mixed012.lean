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

def mixed_012_000 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 3, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(64079547/100000000), 0, (19192791/25000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (560543/100000000)]
    alternative := .zero
    polynomial := [(-518679805801647026543526403/25500310721794000000000000), (-64079547/560543), (-2264922767067603026543526403/12750155360897000000000000), (-64079547/560543), (-4011165728333559026543526403/25500310721794000000000000)]
    bernstein := [(48676831744687163549547798413/104449272716468224000000000000), (127999766553700080280385637161/261123181791170560000000000000), (970227822043515549797898111503/1958423863433779200000000000000), (786924836166601277834152754593/1632019886194816000000000000000), (1839696557843460249798533628797/4080049715487040000000000000000)]
    reserve := (22545026239/50000000000) }

theorem mixed_012_000_valid : mixed_012_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_012_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_012_000]
  · intro i; fin_cases i <;> norm_num [mixed_012_000]
  · norm_num [mixed_012_000]
  · norm_num [mixed_012_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_012_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_012_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_012_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_012_000]

def mixed_012_001 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(60597559/100000000), 0, (19887081/25000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (71153/12500000)]
    alternative := .zero
    polynomial := [(-3562220206639771900012997/202306469885875000000000), (-60597559/569224), (-17698255066183490650012997/101153234942937500000000), (-60597559/569224), (-31834289925727209400012997/202306469885875000000000)]
    bernstein := [(13643920808794202435479791803/32369035181740000000000000000), (28858898127975434405825433177/64738070363480000000000000000), (175343518645345172133590587129/388428422180880000000000000000), (113646782124801563143789401537/258952281453920000000000000000), (211576280700232062890927695083/517904562907840000000000000000)]
    reserve := (51065460669/125000000000) }

theorem mixed_012_001_valid : mixed_012_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_012_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_012_001]
  · intro i; fin_cases i <;> norm_num [mixed_012_001]
  · norm_num [mixed_012_001]
  · norm_num [mixed_012_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_012_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_012_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_012_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_012_001]

def mixed_012_002 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 3, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(28469751/50000000), 0, (41103203/50000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (577517/100000000)]
    alternative := .zero
    polynomial := [(-198022822755422651814753033/13136247305843000000000000), (-56939502/577517), (-1132959525346459651814753033/6568123652921500000000000), (-56939502/577517), (-2067896227937496651814753033/13136247305843000000000000)]
    bernstein := [(12678838078989630820332633898087/33628793102958080000000000000000), (3374686266314741915529127349497/8407198275739520000000000000000), (2569063427926383781645466878321/6305398706804640000000000000000), (207836701201420769012252617917/525449892233720000000000000000), (48086875389600539788919214927/131362473058430000000000000000)]
    reserve := (45757812591/125000000000) }

theorem mixed_012_002_valid : mixed_012_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_012_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_012_002]
  · intro i; fin_cases i <;> norm_num [mixed_012_002]
  · norm_num [mixed_012_002]
  · norm_num [mixed_012_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_012_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_012_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_012_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_012_002]

def mixed_012_003 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(53110117/100000000), 0, (84730841/100000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (585377/100000000)]
    alternative := .zero
    polynomial := [(-339258122900483084710239531/26630062973566000000000000), (-53110117/585377), (-2266552526022922084710239531/13315031486783000000000000), (-53110117/585377), (-4193846929145361084710239531/26630062973566000000000000)]
    bernstein := [(88549459950464372557644132189/266300629735660000000000000000), (380287672412569559930824855393/1065202518942640000000000000000), (4645365163118474467814677763923/12782430227311680000000000000000), (6001359119702808706522473175517/17043240303082240000000000000000), (595968898346582133533498304417/1842512465198080000000000000000)]
    reserve := (80863618239/250000000000) }

theorem mixed_012_003_valid : mixed_012_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_012_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_012_003]
  · intro i; fin_cases i <;> norm_num [mixed_012_003]
  · norm_num [mixed_012_003]
  · norm_num [mixed_012_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_012_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_012_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_012_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_012_003]

def mixed_012_004 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 3, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(24557813/50000000), 0, (21776787/25000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (592757/100000000)]
    alternative := .zero
    polynomial := [(-142966363296431767024359563/13482897549803000000000000), (-49115626/592757), (-1133639398232777767024359563/6741448774901500000000000), (-49115626/592757), (-2124312433169123767024359563/13482897549803000000000000)]
    bernstein := [(9938248941318970912803847564517/34516217727495680000000000000000), (1078736354253315132634199845167/3451621772749568000000000000000), (330618300008552585049716301943/1035486531824870400000000000000), (10650183872248331260186750359/34516217727495680000000000000), (968615640366327329960086293/3451621772749568000000000000)]
    reserve := (280626240109/1000000000000) }

theorem mixed_012_004_valid : mixed_012_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_012_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_012_004]
  · intro i; fin_cases i <;> norm_num [mixed_012_004]
  · norm_num [mixed_012_004]
  · norm_num [mixed_012_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_012_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_012_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_012_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_012_004]

def mixed_012_005 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(44963763/100000000), 0, (44660553/50000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (299807/50000000)]
    alternative := .zero
    polynomial := [(-118196758484062380454882503/13638867413506000000000000), (-44963763/599614), (-1134049225205749380454882503/6819433706753000000000000), (-44963763/599614), (-2149901691927436380454882503/13638867413506000000000000)]
    bernstein := [(849105692367450048538956633/3491550057857536000000000000), (9353509417523663953122568881/34915500578575360000000000000), (96006953498040728465674791801/349155005785753600000000000000), (924388624438164875952884605233/3491550057857536000000000000000), (8292203723430385849430763440217/34915500578575360000000000000000)]
    reserve := (59373369893/250000000000) }

theorem mixed_012_005_valid : mixed_012_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_012_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_012_005]
  · intro i; fin_cases i <;> norm_num [mixed_012_005]
  · norm_num [mixed_012_005]
  · norm_num [mixed_012_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_012_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_012_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_012_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_012_005]

def mixed_012_006 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 3, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1270743/3125000), 0, (22839737/25000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (37869/6250000)]
    alternative := .zero
    polynomial := [(-1491821400650989586193607/215342816412750000000000), (-847162/12623), (-17726648342564208336193607/107671408206375000000000), (-847162/12623), (-11320491761492475695397869/71780938804250000000000)]
    bernstein := [(8405256148349670730035914621/42405970001280000000000000000), (15366968137530188609686246297/68909701252080000000000000000), (114482691873073718952429187/496944960952500000000000000), (39590046990767363728989927/179452347010625000000000000), (502020682995166629483109/2588255004960937500000000)]
    reserve := (193961059491/1000000000000) }

theorem mixed_012_006_valid : mixed_012_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_012_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_012_006]
  · intro i; fin_cases i <;> norm_num [mixed_012_006]
  · norm_num [mixed_012_006]
  · norm_num [mixed_012_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_012_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_012_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_012_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_012_006]

def mixed_012_007 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7245283/20000000), 0, (93207547/100000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (611587/100000000)]
    alternative := .zero
    polynomial := [(-149908395024032739852459171/27822412434746000000000000), (-36226415/611587), (-2270014622482245739852459171/13911206217373000000000000), (-36226415/611587), (-4390120849940458739852459171/27822412434746000000000000)]
    bernstein := [(664678619972722964934400101/4347251942929062500000000000), (12364789713874393557032370839/69556031086865000000000000000), (154746509435791199922404866547/834672373042380000000000000000), (1567400964127936400042029193347/8903171979118720000000000000000), (10678312058515352934453169757629/71225375832949760000000000000000)]
    reserve := (149922860127/1000000000000) }

theorem mixed_012_007_valid : mixed_012_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_012_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_012_007]
  · intro i; fin_cases i <;> norm_num [mixed_012_007]
  · norm_num [mixed_012_007]
  · norm_num [mixed_012_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_012_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_012_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_012_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_012_007]

def mixed_012_008 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 3, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7915969/25000000), 0, (4742731/5000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (616623/100000000)]
    alternative := .zero
    polynomial := [(-28383922986601322088284407/7012877735608500000000000), (-31663876/616623), (-189258864331782107362761469/1168812955934750000000000), (-31663876/616623), (-1107169263004091322088284407/7012877735608500000000000)]
    bernstein := [(1923546670314704326214952201193/17952967003157760000000000000000), (1185601518101417258540009555597/8976483501578880000000000000000), (628052489254716785345585433713/4488241750789440000000000000000), (293839559059889977297067257877/2244120875394720000000000000000), (118110278314806629749696112633/1122060437697360000000000000000)]
    reserve := (52630978843/500000000000) }

theorem mixed_012_008_valid : mixed_012_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_012_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_012_008]
  · intro i; fin_cases i <;> norm_num [mixed_012_008]
  · norm_num [mixed_012_008]
  · norm_num [mixed_012_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_012_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_012_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_012_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_012_008]

def mixed_012_009 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 3, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(13494863/50000000), 0, (96288913/100000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (31049/5000000)]
    alternative := .zero
    polynomial := [(-256520803505416931307083/88280375858875000000000), (-13494863/310490), (-7100880872012063806307083/44140187929437500000000), (-13494863/310490), (-13945240940518710681307083/88280375858875000000000)]
    bernstein := [(859278346389710770269848677/14124860137420000000000000000), (484853562743085921800697639/5649944054968000000000000000), (636332975043539779155421991/6779932865961600000000000000), (15395700448460503810291123/180798209758976000000000000), (865669023315994859102973/14463856780718080000000000)]
    reserve := (29925248723/500000000000) }

theorem mixed_012_009_valid : mixed_012_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_012_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_012_009]
  · intro i; fin_cases i <;> norm_num [mixed_012_009]
  · norm_num [mixed_012_009]
  · norm_num [mixed_012_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_012_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_012_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_012_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_012_009]

def mixed_012_010 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 3, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098431/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(22218793/100000000), 0, (19500077/20000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (4997/800000)]
    alternative := .zero
    polynomial := [(-446272034036696216711469/227324313526000000000000), (-22218793/624625), (-18188283711960016216711469/113662156763000000000000), (-22218793/624625), (-35930295389883336216711469/227324313526000000000000)]
    bernstein := [(515497585685996975761739/37244815528099840000000000), (9043029441827941402823143/232780097050624000000000000), (10804123713835716084279463/229717201036800000000000000), (70131431866865555083472111/1818594508208000000000000000), (30801822991526773326304731/2273243135260000000000000000)]
    reserve := (2709945321/200000000000) }

theorem mixed_012_010_valid : mixed_012_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_012_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_012_010]
  · intro i; fin_cases i <;> norm_num [mixed_012_010]
  · norm_num [mixed_012_010]
  · norm_num [mixed_012_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_012_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_012_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_012_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_012_010]

def mixed_012_011 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/10), (-7/80)⟩
    owners := ![0, 3, 0, 2, 0, 2, 1]
    lambda := ![0, (1/20000000), (11/100000000), (3/20000000), (1/12500000), 0, (99999961/100000000)]
    cone := fun i => (![![0, 0, (12274603/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(232333/1250000), 0, (12282183/12500000), 0, 0]] i.1) i.2
    mu := ![(22746071/100000000), (1/50000000), (1/50000000), (1/20000000), (1/50000000), (3/100000000), (78319/25000000)]
    alternative := .zero
    polynomial := [(-295630985294047200720927181/106886972078940000000000000), (-9293316391269/156638000000), (-17057908855879672521538977181/53443486039470000000000000), (-9293316391269/156638000000), (-33820186726465297842357027181/106886972078940000000000000)]
    bernstein := [(3297153333562349840275726619/1068869720789400000000000000000), (44342697589877513601228519411/2850319255438400000000000000000), (237656909566976379288679322629/12071940375974400000000000000000), (2828684866755044343652954917639/182420432348057600000000000000000), (783228573056073469461985650307/257534728020787200000000000000000)]
    reserve := (3041254199/1000000000000) }

theorem mixed_012_011_valid : mixed_012_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_012_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_012_011]
  · intro i; fin_cases i <;> norm_num [mixed_012_011]
  · norm_num [mixed_012_011]
  · norm_num [mixed_012_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_012_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_012_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_012_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_012_011]

def mixed_012_012 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-7/80), (-3/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 1]
    lambda := ![(539667/10000000), (1045243/10000000), (447357/4000000), (17137933/100000000), (17137933/100000000), (4804461/25000000), (3894653/20000000)]
    cone := fun i => (![![0, 0, (2744619/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(3143653/100000000), 0, 0, 0, 0]] i.1) i.2
    mu := ![(504317/10000000), (1486187/50000000), (127721/25000000), (323183/6250000), (1/100000000), (1626593/25000000), (61133/100000000)]
    alternative := .zero
    polynomial := [(-2784302575200263728521584044834582103067631543/6991813179754075829115384164391575000000000000), (-2499806589737/244532000000), (-224790336238135534073205813184221560255670444043/3495906589877037914557692082195787500000000000), (-2499806589737/244532000000), (-446796369901070804417890042323608538408273256543/6991813179754075829115384164391575000000000000)]
    bernstein := [(119127281113121424386492202046049213356699759175921/16846156931925114468268596198439936000000000000000000), (1444974218690882723586905258901429666240039200555653/143192333921363472980283067686739456000000000000000000), (18458462309176452916721508867489235677958622985167/1614951134451467740379132342331648000000000000000000), (397114808614273308681837892469360921532814708570173/35798083480340868245070766921684864000000000000000000), (162628322057943529859223991899829988876256577701617/17899041740170434122535383460842432000000000000000000)]
    reserve := (1414296229/200000000000) }

theorem mixed_012_012_valid : mixed_012_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_012_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_012_012]
  · intro i; fin_cases i <;> norm_num [mixed_012_012]
  · norm_num [mixed_012_012]
  · norm_num [mixed_012_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_012_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_012_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_012_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_012_012]

def mixed_012_013 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/40), (-1/16)⟩
    owners := ![0, 3, 0, 2, 0, 2, 1]
    lambda := ![(354237/6250000), (683949/6250000), (5792779/50000000), (1071901/6250000), (1071901/6250000), (583209/3125000), (18839947/100000000)]
    cone := fun i => (![![0, 0, (198949/4000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1289153/50000000), 0, 0, 0, 0]] i.1) i.2
    mu := ![(98599/2000000), (3113989/100000000), (455477/100000000), (2614847/50000000), (1/100000000), (1601123/25000000), (59251/100000000)]
    alternative := .zero
    polynomial := [(-477758561516490485504796900800589353279631336933/1734573485062508448580033355452362850000000000000), (-997438751603/118502000000), (-54357924653645080789289344552279905926873007336933/867286742531254224290016677726181425000000000000), (-997438751603/118502000000), (-108238090745773671093073892203759222500466383336933/1734573485062508448580033355452362850000000000000)]
    bernstein := [(21633192830337287072029193024021063939934656097558027/4440508121760021628364885389958048896000000000000000000), (13912926238633023106263013593539565430056264602498329/1776203248704008651345954155983219558400000000000000000), (6505468732077058866382683635792709225094031245200179/710481299481603460538381662393287823360000000000000000), (2514311938180187381880344089565395140804592226484817/284192519792641384215352664957315129344000000000000000), (785375317982549427566809473247294867673153362912283/113677007917056553686141065982926051737600000000000000)]
    reserve := (4871783191/1000000000000) }

theorem mixed_012_013_valid : mixed_012_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_012_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_012_013]
  · intro i; fin_cases i <;> norm_num [mixed_012_013]
  · norm_num [mixed_012_013]
  · norm_num [mixed_012_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_012_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_012_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_012_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_012_013]

def mixed_012_014 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/16), (-1/20)⟩
    owners := ![0, 3, 0, 2, 0, 2, 1]
    lambda := ![(2971699/50000000), (11442057/100000000), (1198719/10000000), (8575791/50000000), (8575791/50000000), (1810463/10000000), (9109781/50000000)]
    cone := fun i => (![![0, 0, (2230589/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(510809/25000000), 0, 0, 0, 0]] i.1) i.2
    mu := ![(4820181/100000000), (101811/3125000), (197023/50000000), (5287413/100000000), (1/100000000), (630159/10000000), (11477/20000000)]
    alternative := .zero
    polynomial := [(-325150620359236043095163558749785668338296969/1825877803709661377542985008221080000000000000), (-19270034932261/2869250000000), (-55980106726241363962222624580868745997147696969/912938901854830688771492504110540000000000000), (-19270034932261/2869250000000), (-111635062832123491881350085602987706325957096969/1825877803709661377542985008221080000000000000)]
    bernstein := [(341668796680868103756445001339131778692117014519/119660727743916368038657065498776698880000000000000), (861684360560993017666836243971474042619616308407/149575909679895460048321331873470873600000000000000), (3962840975885133786428392791252902161568682340309/560909661299607975181204994525515776000000000000000), (1582705527849995725415116665461694599291146493351/233712358874836656325502081052298240000000000000000), (1426970246380854868682219182847793334718965487831/292140448593545820406877601315372800000000000000000)]
    reserve := (713828177/250000000000) }

theorem mixed_012_014_valid : mixed_012_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_012_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_012_014]
  · intro i; fin_cases i <;> norm_num [mixed_012_014]
  · norm_num [mixed_012_014]
  · norm_num [mixed_012_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_012_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_012_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_012_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_012_014]

def mixed_012_015 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/20), (-3/80)⟩
    owners := ![0, 3, 0, 2, 0, 2, 1]
    lambda := ![(1555817/25000000), (11948901/100000000), (12388423/100000000), (1071349/6250000), (1071349/6250000), (701779/4000000), (8805883/50000000)]
    cone := fun i => (![![0, 0, (3951597/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(769043/50000000), 0, 0, 0, 0]] i.1) i.2
    mu := ![(4713761/100000000), (851051/25000000), (20407/6250000), (5344089/100000000), (1/100000000), (6197837/100000000), (11107/20000000)]
    alternative := .zero
    polynomial := [(-86513570816910718617300134412608479097680777/830816098656229839421719138936050400000000000), (-14207787576973/2776750000000), (-727394054745547187860909453390854458419421698283/12046833430515332671614927514572730800000000000), (-14207787576973/2776750000000), (-1452279215937403964881917202883743270945010654033/24093666861030665343229855029145461600000000000)]
    bernstein := [(3914994922506333353362601169875320657491897631567/3854986697764906454916776804663273856000000000000000), (59660709314334399017414547117618188700154554749501/15419946791059625819667107218653095424000000000000000), (952321207293221712439945881497194505511164889485509/185039361492715509836005286623837145088000000000000000), (92074333570147940884633728188649858939465820014793/18978396050534924085744131961419194368000000000000000), (7816003592306961039676295757952883179581722310551/2617709800073782632516431994678509568000000000000000)]
    reserve := (1015566389/1000000000000) }

theorem mixed_012_015_valid : mixed_012_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_012_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_012_015]
  · intro i; fin_cases i <;> norm_num [mixed_012_015]
  · norm_num [mixed_012_015]
  · norm_num [mixed_012_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_012_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_012_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_012_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_012_015]

def mixed_012_016 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/80), (-1/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 1]
    lambda := ![(750249/10000000), (290899/2000000), (14927443/100000000), (20119867/100000000), (20119867/100000000), (5690783/50000000), (11403817/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4369151/100000000), 0], ![(712043/100000000), 0, 0, 0, 0]] i.1) i.2
    mu := ![(431149/12500000), (2067669/50000000), (29531/10000000), (1582579/25000000), (1/100000000), (21986/390625), (35991/100000000)]
    alternative := .zero
    polynomial := [(-6335844131727549329284491848091068044467217/189063576194322510662655662697600000000000000), (-9166982659031/3599100000000), (-456714257808447101055439620290363781180051913/10503532010795695036814203483200000000000000), (-9166982659031/3599100000000), (-8214520796420320269668628673378456993196467217/189063576194322510662655662697600000000000000)]
    bernstein := [(6996309755642107726313281731038429607050614437023/7744044080919450036742375944093696000000000000000000), (12120017150989251903774494878439798497593624809141/3872022040459725018371187972046848000000000000000000), (2724891689597653673496600300668543981928169988749/645337006743287503061864662007808000000000000000000), (4048415032535863034296908558958062290414281822349/968005510114931254592796993011712000000000000000000), (1457043270099502486834928806645587906945872918383/484002755057465627296398496505856000000000000000000)]
    reserve := (903443947/1000000000000) }

theorem mixed_012_016_valid : mixed_012_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_012_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_012_016]
  · intro i; fin_cases i <;> norm_num [mixed_012_016]
  · norm_num [mixed_012_016]
  · norm_num [mixed_012_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_012_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_012_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_012_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_012_016]

def mixed_012_017 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/40), (-1/80)⟩
    owners := ![0, 3, 0, 2, 0, 2, 1]
    lambda := ![(733923/10000000), (3007439/20000000), (15281247/100000000), (20575509/100000000), (20575509/100000000), (1059193/10000000), (529969/5000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (499179/10000000), 0], ![(397337/100000000), 0, 0, 0, 0]] i.1) i.2
    mu := ![(407203/12500000), (2114003/50000000), (100571/50000000), (3238023/50000000), (1/100000000), (5568741/100000000), (3347/10000000)]
    alternative := .zero
    polynomial := [(-97544924793779665983797612860811723095404271/10244996672180064068844550355616900000000000000), (-130452892109/83675000000), (-230440745540580425182286998661420720878919154271/5122498336090032034422275177808450000000000000), (-130452892109/83675000000), (-460783946156367070698590199709980630034742904271/10244996672180064068844550355616900000000000000)]
    bernstein := [(35285458249955083261194386951562979988123909668529/26227191480780964016242048910379264000000000000000000), (61233178910084718203021161989754970879285349691643/17484794320520642677494699273586176000000000000000000), (1411839740253880685622423501386929681708301117330387/314726297769371568194904586924551168000000000000000000), (300623255274964537979237992227636433809791315338043/69939177282082570709978797094344704000000000000000000), (1233597263990798674762546571959596501739958902266929/419635063692495424259872782566068224000000000000000000)]
    reserve := (53815077/40000000000) }

theorem mixed_012_017_valid : mixed_012_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_012_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_012_017]
  · intro i; fin_cases i <;> norm_num [mixed_012_017]
  · norm_num [mixed_012_017]
  · norm_num [mixed_012_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_012_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_012_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_012_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_012_017]

def mixed_012_018 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/80), 0⟩
    owners := ![0, 3, 0, 2, 0, 2, 1]
    lambda := ![(179239/2500000), (7765547/50000000), (15617339/100000000), (10496121/50000000), (10496121/50000000), (4924189/50000000), (9849147/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (1392983/25000000), 0], ![(12311/10000000), 0, 0, 0, 0]] i.1) i.2
    mu := ![(1539111/50000000), (4322361/100000000), (2519/2500000), (6611219/100000000), (1/100000000), (5510347/100000000), (31109/100000000)]
    alternative := .zero
    polynomial := [(282818438254536899806266497982608573322608167/158264839751465709324791026449926775000000000000), (-83801618987/119650000000), (-336306666368610493555949994606249344363259211391/6087109221210219589415039478843337500000000000), (-83801618987/119650000000), (-8744256144022127369354506126260465562018062104333/158264839751465709324791026449926775000000000000)]
    bernstein := [(12376628199409086202182967430923623021073415242753267/6482527836220035453943440443389000704000000000000000000), (743494704211252687373081186449570068392692898369/184162722619887370850665921687187520000000000000000), (2051396231409754969495740143525287828242721008331/434097846175448802719426815405513440000000000000000), (1258430952976423420780096234157517754282056959/316529679502931418649582052899853550000000000000), (282818438254536899806266497982608573322608167/158264839751465709324791026449926775000000000000)]
    reserve := (1786994753/1000000000000) }

theorem mixed_012_018_valid : mixed_012_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_012_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_012_018]
  · intro i; fin_cases i <;> norm_num [mixed_012_018]
  · norm_num [mixed_012_018]
  · norm_num [mixed_012_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_012_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_012_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_012_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_012_018]

def mixed_012_019 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨0, (1/80)⟩
    owners := ![0, 3, 0, 2, 0, 2, 1]
    lambda := ![(3488341/50000000), (3995243/25000000), (15979723/100000000), (21376337/100000000), (21376337/100000000), (9172567/100000000), (4568691/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(99877/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (1220377/20000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(45389/1562500), (2203051/50000000), (2019/4000000), (6743761/100000000), (1/100000000), (2729113/50000000), (58507/100000000)]
    alternative := .zero
    polynomial := [(51608761629876272385410043282049127000879183/21739172216221612868803008586439100000000000000), (1028670448447/1261875000000), (-235197011041858896667923031601513790915787266939/3623195369370268811467168097739850000000000000), (1028670448447/1261875000000), (-1411233675012783256279923599652364794621724480817/21739172216221612868803008586439100000000000000)]
    bernstein := [(51608761629876272385410043282049127000879183/21739172216221612868803008586439100000000000000), (35662920570143047834665504784552202445773561/7246390738740537622934336195479700000000000000), (3810251490144199037519469550332589432209908551/659387214141319063319143388403840000000000000000), (229352140950775710536944671082169423332759403961/46376900727939440786779751651070080000000000000000), (2155795359877182259171714269766553035814346823141583/890436493976437263106171231700545536000000000000000000)]
    reserve := (296749809/125000000000) }

theorem mixed_012_019_valid : mixed_012_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_012_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_012_019]
  · intro i; fin_cases i <;> norm_num [mixed_012_019]
  · norm_num [mixed_012_019]
  · norm_num [mixed_012_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_012_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_012_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_012_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_012_019]

def mixed_012_020 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/80), (1/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 1]
    lambda := ![(6762207/100000000), (4096107/25000000), (1023307/6250000), (21732753/100000000), (21732753/100000000), (8554141/100000000), (4230403/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(3071/500000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (3294653/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1368401/50000000), (4478763/100000000), (25869/50000000), (3437713/50000000), (1/100000000), (1352853/25000000), (110007/100000000)]
    alternative := .zero
    polynomial := [(-1171835439889985686040877697567648475192484653/100139780080448943254928197393750100000000000000), (455783584969/215575000000), (-325189374757573523445402190992149758404679720517/5563321115580496847496010966319450000000000000), (455783584969/215575000000), (-5852236910196433436331198560161128002809042484653/100139780080448943254928197393750100000000000000)]
    bernstein := [(2550309586636348445560680062939317889970911636341883/455747265788354301746873218360889344000000000000000000), (15664601740790425612830231893206060612032594251406547/2050862696047594357860929482624002048000000000000000000), (929572259703561137389883630430751483694382918948283/113936816447088575436718304590222336000000000000000000), (3669670261891701253988794821568943835065290207820947/512715674011898589465232370656000512000000000000000000), (395833660296902227303874447870798854221298258315249/85452612335316431577538728442666752000000000000000000)]
    reserve := (1158050203/250000000000) }

theorem mixed_012_020_valid : mixed_012_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_012_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_012_020]
  · intro i; fin_cases i <;> norm_num [mixed_012_020]
  · norm_num [mixed_012_020]
  · norm_num [mixed_012_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_012_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_012_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_012_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_012_020]

def mixed_012_021 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 3, 0, 2, 0, 2, 1]
    lambda := ![(321767/5000000), (2123809/12500000), (8471377/50000000), (22211399/100000000), (22211399/100000000), (1920349/25000000), (7527239/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(79531/6250000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (3632501/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(500467/20000000), (71731/1562500), (5361/5000000), (882349/12500000), (1/100000000), (2670499/50000000), (19581/10000000)]
    alternative := .zero
    polynomial := [(-1629196108017956380125719842993551758453/53073035091379485982981309700000000000000), (2904306098659/1340250000000), (-2377328113181357269156985742780228972675359/79609552637069228974471964550000000000000), (2904306098659/1340250000000), (-4749768638038660669173594326031477290075359/159219105274138457948943929100000000000000)]
    bernstein := [(657011823732667803831524152457208788297911947/135866969833931484116432152832000000000000000000), (1846663284101983334253967567695564882435543041/203800454750897226174648229248000000000000000000), (3112395066283076264820653558524622840572627123/305700682126345839261972343872000000000000000000), (417417065312271285893388852314942383074613841/50950113687724306543662057312000000000000000000), (78481662044243476993200580984252171944197441/25475056843862153271831028656000000000000000000)]
    reserve := (385090711/125000000000) }

theorem mixed_012_021_valid : mixed_012_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_012_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_012_021]
  · intro i; fin_cases i <;> norm_num [mixed_012_021]
  · norm_num [mixed_012_021]
  · norm_num [mixed_012_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_012_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_012_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_012_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_012_021]

def mixed_012_022 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 1]
    lambda := ![(5992813/100000000), (17804433/100000000), (17665877/100000000), (11375493/50000000), (11375493/50000000), (6615543/100000000), (6419363/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1108447/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (8067721/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(443803/20000000), (296677/6250000), (7007/6250000), (7278283/100000000), (1/100000000), (5246969/100000000), (62811/25000000)]
    alternative := .zero
    polynomial := [(-93198664214798663467312829676441332670823/954417861051612067470542126175000000000000), (20454957970207/5605600000000), (-371486641575569967714876017643453848674894523/12407432193670956877117047640275000000000000), (20454957970207/5605600000000), (-2892773897974824883514069928575469619923233/96933064013054350602476934689648437500000)]
    bernstein := [(362273130272478510807452623050674761216733071/35449806267631305363191564686500000000000000000), (28568049645057202456138741462880344816068840889/1985189150987353100338727622444000000000000000000), (92033936063469783977499806609788876505497111013/5955567452962059301016182867332000000000000000000), (106396379648719850941618999339292386356286333751/7940756603949412401354910489776000000000000000000), (16290268615566497606888892520969622224471037441/1985189150987353100338727622444000000000000000000)]
    reserve := (8205902499/1000000000000) }

theorem mixed_012_022_valid : mixed_012_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_012_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_012_022]
  · intro i; fin_cases i <;> norm_num [mixed_012_022]
  · norm_num [mixed_012_022]
  · norm_num [mixed_012_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_012_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_012_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_012_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_012_022]

def mixed_012_023 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 3, 0, 2, 0, 2, 1]
    lambda := ![(3188127/50000000), (20956911/100000000), (10319223/50000000), (13007097/50000000), (13007097/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (3188127/100000000), 0], ![0, 0, 0, 0, 0], ![(1819797/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (13007097/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1139257/100000000), (5535069/100000000), (16439/12500000), (1048833/12500000), (1/100000000), (2324001/50000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-18256012853918688581681415938937306822701/77986204468016575713044757275000000000000), (38137323767067/6575600000000), (-1300665340940823177984992885258778636728951/38993102234008287856522378637500000000000), (38137323767067/6575600000000), (-2583074669027727667388304354578619966635201/77986204468016575713044757275000000000000)]
    bernstein := [(172206554701828468754792818528038647608629407/11743804908124849048552622272000000000000000000), (993399460026777484312914705068142356396677423/49911170859530608456348644656000000000000000000), (811853769901994448202551965162101768335839773/37433378144647956342261483492000000000000000000), (62393001043206638716748097922113708606632447/3119448178720663028521790291000000000000000000), (11553064398536739146537575174347245662439599/779862044680165757130447572750000000000000000)]
    reserve := (1832951033/125000000000) }

theorem mixed_012_023_valid : mixed_012_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_012_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_012_023]
  · intro i; fin_cases i <;> norm_num [mixed_012_023]
  · norm_num [mixed_012_023]
  · norm_num [mixed_012_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_012_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_012_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_012_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_012_023]

def mixed_012_024 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 3, 0, 2, 0, 2, 1]
    lambda := ![0, (918193/4000000), (22381043/100000000), (13666033/50000000), (13666033/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (1359881/20000000), 0, 0], ![(1020057/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (13666033/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (5967013/100000000), (71691/50000000), (8926269/100000000), (1/100000000), (1220867/25000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-66900454383404702082285483995855785723/155395591181861456780940300000000000000), (312203065667/38235200000), (-950298314424645651732714886467924845241/25899265196976909463490050000000000000), (312203065667/38235200000), (-5634889432164469208314003834811693285723/155395591181861456780940300000000000000)]
    bernstein := [(12242195950854464807862751876111222446559/517985303939538189269801000000000000000000), (1590543498440763263329239787567024923919/54050640411082245836848800000000000000000), (10418055657019475340625927160442238496811/331510594521304441132672640000000000000000), (362398628205502555521081345342745106437/12240391182325087057206374400000000000000), (15622203324033291152409946651335761867/652820863057337976384339968000000000000)]
    reserve := (11817126719/500000000000) }

theorem mixed_012_024_valid : mixed_012_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_012_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_012_024]
  · intro i; fin_cases i <;> norm_num [mixed_012_024]
  · norm_num [mixed_012_024]
  · norm_num [mixed_012_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_012_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_012_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_012_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_012_024]

def mixed_012_025 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 3, 0, 2, 0, 2, 1]
    lambda := ![0, (147343/625000), (5674999/25000000), (13431281/50000000), (13431281/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (698307/10000000), 0, 0], ![(1272559/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (13431281/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3064097/50000000), (29279/20000000), (1777321/20000000), (1/100000000), (4799581/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1499037243047114636399256772745598759/2250862833049336788686950000000000000), (187502660737/18299375000), (-42639394791385283187981794943529598759/1125431416524668394343475000000000000), (187502660737/18299375000), (-83779752339723451739564333114313598759/2250862833049336788686950000000000000)]
    bernstein := [(957547437192736028789336620969616133/28367797428215641496805376000000000000), (14106053388858314002162196781766602283/354597467852695518710067200000000000000), (1034638847175989611798662664697815733749/24695180796884152195879680000000000000000), (5772266176894417183213982023958111533747/144055221315157554475964800000000000000000), (12336004350024842102317413662726085995721/360138053287893886189912000000000000000000)]
    reserve := (8438683331/250000000000) }

theorem mixed_012_025_valid : mixed_012_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_012_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_012_025]
  · intro i; fin_cases i <;> norm_num [mixed_012_025]
  · norm_num [mixed_012_025]
  · norm_num [mixed_012_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_012_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_012_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_012_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_012_025]

def mixed_012_026 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 1]
    lambda := ![0, (12114981/50000000), (11491619/50000000), (131967/500000), (131967/500000), 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (7177111/100000000), 0, 0], ![(1534429/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (131967/1000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (78731/1250000), (4669/3125000), (353729/4000000), (1/100000000), (943151/20000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-137429171232637526467004650211489/142704879100409655948800000000000), (18589578180849/1494080000000), (-2796922599157646432715179498219489/71352439550204827974400000000000), (18589578180849/1494080000000), (-5456416027082655338963354346227489/142704879100409655948800000000000)]
    bernstein := [(1003677543335807446820032379302612591/22832780656065544951808000000000000000), (2294537935765625080263698800425096179/45665561312131089903616000000000000000), (70857303078098812040185219960598351/1349721024003874578432000000000000000), (1322219814542503551718785500240313517/26094606464074908516352000000000000000), (16332966250647728906970070987860883711/365324490497048719228928000000000000000)]
    reserve := (549471809/12500000000) }

theorem mixed_012_026_valid : mixed_012_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_012_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_012_026]
  · intro i; fin_cases i <;> norm_num [mixed_012_026]
  · norm_num [mixed_012_026]
  · norm_num [mixed_012_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_012_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_012_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_012_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_012_026]

def mixed_012_027 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 3, 0, 2, 0, 2, 1]
    lambda := ![0, (3115391/12500000), (5807559/25000000), (12961659/50000000), (12961659/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (230701/3125000), 0, 0], ![(2257189/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (12961659/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3239333/50000000), (152427/100000000), (8795523/100000000), (1/100000000), (926353/20000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-8088291047042507067469792955964576067/6095533786459911271930650000000000000), (639275117809/43303125000), (-3995256608189536789524106100079115357/98315061071934052773075000000000000), (639275117809/43303125000), (-21783419878246252171184071386267325097/554139435132719206539150000000000000)]
    bernstein := [(16614866608406752723758915701067532118383/305971892026222997179264000000000000000000), (2328654592841885223650645054058504383569/38246486503277874647408000000000000000000), (11573741877916574739098259603843563478419/182866013593797338157919500000000000000000), (312234845022086266579014789812883267901/5079611488716592726608875000000000000000), (52719263611368491492730091719762644677/952427154134361136239164062500000000000)]
    reserve := (27150968833/500000000000) }

theorem mixed_012_027_valid : mixed_012_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_012_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_012_027]
  · intro i; fin_cases i <;> norm_num [mixed_012_027]
  · norm_num [mixed_012_027]
  · norm_num [mixed_012_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_012_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_012_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_012_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_012_027]

def mixed_012_028 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 1]
    lambda := ![0, (17205493/50000000), (6287503/20000000), (68303/200000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (10192813/100000000), 0, 0], ![(6996403/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(68303/4000000), 0, (68303/200000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2236249/25000000), (104249/50000000), (2932233/25000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-5227173626646010439841757245757/2187461975786106345600000000000), (120376562841679/5212450000000), (-61975616579157197887931648685757/1093730987893053172800000000000), (120376562841679/5212450000000), (-118724059531668385336021540125757/2187461975786106345600000000000)]
    bernstein := [(20691729972029707903540686187067/341790933716579116500000000000000), (381064043993711265069014888518231/5468654939465265864000000000000000), (4791054281677297143897762362300381/65623859273583190368000000000000000), (49306229729091165869690519337038947/699987832251554030592000000000000000), (346485855389116109200180648629093923/5599902658012432244736000000000000000)]
    reserve := (7567392787/125000000000) }

theorem mixed_012_028_valid : mixed_012_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_012_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_012_028]
  · intro i; fin_cases i <;> norm_num [mixed_012_028]
  · norm_num [mixed_012_028]
  · norm_num [mixed_012_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_012_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_012_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_012_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_012_028]

def mixed_012_029 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 3, 0, 2, 0, 2, 1]
    lambda := ![0, (35128443/100000000), (15688557/50000000), (33494443/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (10405329/100000000), 0, 0], ![(1579507/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(837361/50000000), 0, (33494443/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1141437/12500000), (42127/20000000), (5798443/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-680837497937424188277681944896733/223055973485128845600000000000000), (55485621617601/2106350000000), (-6516971056777677820436068890496733/111527986742564422800000000000000), (55485621617601/2106350000000), (-12353104615617931452594455836096733/223055973485128845600000000000000)]
    bernstein := [(42581088254143066137432764315939661187/571023292121929844736000000000000000000), (4802148092181189983505756023035218763/57102329212192984473600000000000000000), (1501295710738556370833377928515678633/17130698763657895342080000000000000000), (48593796184316014153653579844486091/571023292121929844736000000000000000), (4360852491804169771928361582444163/57102329212192984473600000000000000)]
    reserve := (74569792233/1000000000000) }

theorem mixed_012_029_valid : mixed_012_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_012_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_012_029]
  · intro i; fin_cases i <;> norm_num [mixed_012_029]
  · norm_num [mixed_012_029]
  · norm_num [mixed_012_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_012_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_012_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_012_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_012_029]

def mixed_012_030 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 1]
    lambda := ![0, (17949483/50000000), (15635283/50000000), (8207617/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2126713/20000000), 0, 0], ![(8816001/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1641523/100000000), 0, (8207617/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (933179/10000000), (106397/50000000), (5728217/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1302572615901372155992822807109243/341244021854795802600000000000000), (158242660077483/5319850000000), (-10303626461304082979442645769109243/170622010927397901300000000000000), (158242660077483/5319850000000), (-19304680306706793802892468731109243/341244021854795802600000000000000)]
    bernstein := [(7757550702793850456277661941428773/87358469594827725465600000000000000), (28757701512463641711828308303143533/291194898649425751552000000000000000), (2687252250113901359654463417806128423/26207540878448317639680000000000000000), (2912995901525714722651776850652589429/29119489864942575155200000000000000000), (79606664601623983972680726271788603637/873584695948277254656000000000000000000)]
    reserve := (11100169707/125000000000) }

theorem mixed_012_030_valid : mixed_012_030.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_012_030]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_012_030]
  · intro i; fin_cases i <;> norm_num [mixed_012_030]
  · norm_num [mixed_012_030]
  · norm_num [mixed_012_030, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_012_030, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_012_030, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_012_030, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_012_030]

def mixed_012_031 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 3, 0, 2, 0, 2, 1]
    lambda := ![0, (7344919/20000000), (31117059/100000000), (16079173/50000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (5439061/50000000), 0, 0], ![(780179/4000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1607917/100000000), 0, (16079173/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (9546409/100000000), (214977/100000000), (11307057/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-151218833152678300452622318104043/32229169918195838612500000000000), (5730351560501/171981600000), (-143975419339764645118255500666649/2302083565585417043750000000000), (5730351560501/171981600000), (-1864437037604026731202954691229043/32229169918195838612500000000000)]
    bernstein := [(25568139385763867237214602475565155511/247520024971744040544000000000000000000), (34667302879850396887185801376693801/304827616960275912000000000000000000), (607312373992507999815549129820113873/5156667186911334178000000000000000000), (445972825902422060839338379743260087/3867500390183500633500000000000000000), (34230139033925980989796546038990117/322291699181958386125000000000000000)]
    reserve := (25824314001/250000000000) }

theorem mixed_012_031_valid : mixed_012_031.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_012_031]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_012_031]
  · intro i; fin_cases i <;> norm_num [mixed_012_031]
  · norm_num [mixed_012_031]
  · norm_num [mixed_012_031, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_012_031, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_012_031, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_012_031, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_012_031]

def mixed_012_032 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 3, 0, 2, 0, 2, 1]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2962081/10000000), 0, 0], ![(28469751/50000000), 0, (41103203/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (812331/3125000), (577517/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-229823287470729909864305101/15012318788064000000000000), (56939502/577517), (-1298284279348905909864305101/7506159394032000000000000), (56939502/577517), (-2366745271227081909864305101/15012318788064000000000000)]
    bernstein := [(13138588271588308902191095019/150123187880640000000000000000), (69104768566036171083136612049/600492751522560000000000000000), (900737018833400756137339380437/7205913018270720000000000000000), (1123388895539770296569437309309/9607884024360960000000000000000), (3475613136074926185128324829539/38431536097443840000000000000000)]
    reserve := (87518713511/1000000000000) }

theorem mixed_012_032_valid : mixed_012_032.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_012_032]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_012_032]
  · intro i; fin_cases i <;> norm_num [mixed_012_032]
  · norm_num [mixed_012_032]
  · norm_num [mixed_012_032, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_012_032, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_012_032, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_012_032, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_012_032]

def mixed_012_033 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 3, 0, 2, 0, 2, 1]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2962081/10000000), 0, 0], ![(60597559/100000000), 0, (19887081/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (812331/3125000), (71153/12500000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-33001336618930860110602801/1849593204576000000000000), (60597559/569224), (-162240475785418860110602801/924796602288000000000000), (60597559/569224), (-291479614951906860110602801/1849593204576000000000000)]
    bernstein := [(577366111911772817423908059839/4734958603714560000000000000000), (39504985418009181970020858069/263053255761920000000000000000), (570164505889119181559372097557/3551218952785920000000000000000), (10040759707352501223594892749/65763313940480000000000000000), (37320256698406454842364715599/295934912732160000000000000000)]
    reserve := (15242110867/125000000000) }

theorem mixed_012_033_valid : mixed_012_033.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_012_033]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_012_033]
  · intro i; fin_cases i <;> norm_num [mixed_012_033]
  · norm_num [mixed_012_033]
  · norm_num [mixed_012_033, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_012_033, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_012_033, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_012_033, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_012_033]

def mixed_012_034 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 3, 0, 2, 0, 2, 1]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2962081/10000000), 0, 0], ![(64079547/100000000), 0, (19192791/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (812331/3125000), (560543/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-59958801475902553849305923/2914217316691200000000000), (64079547/560543), (-259522310030411353849305923/1457108658345600000000000), (64079547/560543), (-459085818584920153849305923/2914217316691200000000000)]
    bernstein := [(72505118810180351826076617277/466274770670592000000000000000), (34406218523311005620756943713/186509908268236800000000000000), (43719098275374436767077075023/223811889921884160000000000000), (5600598990409757589120839401/29841585322917888000000000000), (1921973299653056937048736333/11936634129167155200000000000)]
    reserve := (31099739197/200000000000) }

theorem mixed_012_034_valid : mixed_012_034.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_012_034]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_012_034]
  · intro i; fin_cases i <;> norm_num [mixed_012_034]
  · norm_num [mixed_012_034]
  · norm_num [mixed_012_034, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_012_034, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_012_034, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_012_034, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_012_034]

def mixedTable012 : OwnerTable where
  mode := .mixed
  owners := ![0, 3, 0, 2, 0, 2, 1]
  rows := [mixed_012_000, mixed_012_001, mixed_012_002, mixed_012_003, mixed_012_004, mixed_012_005, mixed_012_006, mixed_012_007, mixed_012_008, mixed_012_009, mixed_012_010, mixed_012_011, mixed_012_012, mixed_012_013, mixed_012_014, mixed_012_015, mixed_012_016, mixed_012_017, mixed_012_018, mixed_012_019, mixed_012_020, mixed_012_021, mixed_012_022, mixed_012_023, mixed_012_024, mixed_012_025, mixed_012_026, mixed_012_027, mixed_012_028, mixed_012_029, mixed_012_030, mixed_012_031, mixed_012_032, mixed_012_033, mixed_012_034]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact mixed_012_000_valid
    · exact mixed_012_001_valid
    · exact mixed_012_002_valid
    · exact mixed_012_003_valid
    · exact mixed_012_004_valid
    · exact mixed_012_005_valid
    · exact mixed_012_006_valid
    · exact mixed_012_007_valid
    · exact mixed_012_008_valid
    · exact mixed_012_009_valid
    · exact mixed_012_010_valid
    · exact mixed_012_011_valid
    · exact mixed_012_012_valid
    · exact mixed_012_013_valid
    · exact mixed_012_014_valid
    · exact mixed_012_015_valid
    · exact mixed_012_016_valid
    · exact mixed_012_017_valid
    · exact mixed_012_018_valid
    · exact mixed_012_019_valid
    · exact mixed_012_020_valid
    · exact mixed_012_021_valid
    · exact mixed_012_022_valid
    · exact mixed_012_023_valid
    · exact mixed_012_024_valid
    · exact mixed_012_025_valid
    · exact mixed_012_026_valid
    · exact mixed_012_027_valid
    · exact mixed_012_028_valid
    · exact mixed_012_029_valid
    · exact mixed_012_030_valid
    · exact mixed_012_031_valid
    · exact mixed_012_032_valid
    · exact mixed_012_033_valid
    · exact mixed_012_034_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
