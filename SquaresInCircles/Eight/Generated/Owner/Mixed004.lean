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

def mixed_004_000 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(64079547/100000000), 0, (19192791/25000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (560543/100000000)]
    alternative := .zero
    polynomial := [(-518679805801647026543526403/25500310721794000000000000), (-64079547/560543), (-2264922767067603026543526403/12750155360897000000000000), (-64079547/560543), (-4011165728333559026543526403/25500310721794000000000000)]
    bernstein := [(48676831744687163549547798413/104449272716468224000000000000), (127999766553700080280385637161/261123181791170560000000000000), (970227822043515549797898111503/1958423863433779200000000000000), (786924836166601277834152754593/1632019886194816000000000000000), (1839696557843460249798533628797/4080049715487040000000000000000)]
    reserve := (22545026239/50000000000) }

theorem mixed_004_000_valid : mixed_004_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_000]
  · intro i; fin_cases i <;> norm_num [mixed_004_000]
  · norm_num [mixed_004_000]
  · norm_num [mixed_004_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_000]

def mixed_004_001 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(60597559/100000000), 0, (19887081/25000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (71153/12500000)]
    alternative := .zero
    polynomial := [(-3562220206639771900012997/202306469885875000000000), (-60597559/569224), (-17698255066183490650012997/101153234942937500000000), (-60597559/569224), (-31834289925727209400012997/202306469885875000000000)]
    bernstein := [(13643920808794202435479791803/32369035181740000000000000000), (28858898127975434405825433177/64738070363480000000000000000), (175343518645345172133590587129/388428422180880000000000000000), (113646782124801563143789401537/258952281453920000000000000000), (211576280700232062890927695083/517904562907840000000000000000)]
    reserve := (51065460669/125000000000) }

theorem mixed_004_001_valid : mixed_004_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_001]
  · intro i; fin_cases i <;> norm_num [mixed_004_001]
  · norm_num [mixed_004_001]
  · norm_num [mixed_004_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_001]

def mixed_004_002 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(28469751/50000000), 0, (41103203/50000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (577517/100000000)]
    alternative := .zero
    polynomial := [(-198022822755422651814753033/13136247305843000000000000), (-56939502/577517), (-1132959525346459651814753033/6568123652921500000000000), (-56939502/577517), (-2067896227937496651814753033/13136247305843000000000000)]
    bernstein := [(12678838078989630820332633898087/33628793102958080000000000000000), (3374686266314741915529127349497/8407198275739520000000000000000), (2569063427926383781645466878321/6305398706804640000000000000000), (207836701201420769012252617917/525449892233720000000000000000), (48086875389600539788919214927/131362473058430000000000000000)]
    reserve := (45757812591/125000000000) }

theorem mixed_004_002_valid : mixed_004_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_002]
  · intro i; fin_cases i <;> norm_num [mixed_004_002]
  · norm_num [mixed_004_002]
  · norm_num [mixed_004_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_002]

def mixed_004_003 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(53110117/100000000), 0, (84730841/100000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (585377/100000000)]
    alternative := .zero
    polynomial := [(-339258122900483084710239531/26630062973566000000000000), (-53110117/585377), (-2266552526022922084710239531/13315031486783000000000000), (-53110117/585377), (-4193846929145361084710239531/26630062973566000000000000)]
    bernstein := [(88549459950464372557644132189/266300629735660000000000000000), (380287672412569559930824855393/1065202518942640000000000000000), (4645365163118474467814677763923/12782430227311680000000000000000), (6001359119702808706522473175517/17043240303082240000000000000000), (595968898346582133533498304417/1842512465198080000000000000000)]
    reserve := (80863618239/250000000000) }

theorem mixed_004_003_valid : mixed_004_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_003]
  · intro i; fin_cases i <;> norm_num [mixed_004_003]
  · norm_num [mixed_004_003]
  · norm_num [mixed_004_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_003]

def mixed_004_004 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(24557813/50000000), 0, (21776787/25000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (592757/100000000)]
    alternative := .zero
    polynomial := [(-142966363296431767024359563/13482897549803000000000000), (-49115626/592757), (-1133639398232777767024359563/6741448774901500000000000), (-49115626/592757), (-2124312433169123767024359563/13482897549803000000000000)]
    bernstein := [(9938248941318970912803847564517/34516217727495680000000000000000), (1078736354253315132634199845167/3451621772749568000000000000000), (330618300008552585049716301943/1035486531824870400000000000000), (10650183872248331260186750359/34516217727495680000000000000), (968615640366327329960086293/3451621772749568000000000000)]
    reserve := (280626240109/1000000000000) }

theorem mixed_004_004_valid : mixed_004_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_004]
  · intro i; fin_cases i <;> norm_num [mixed_004_004]
  · norm_num [mixed_004_004]
  · norm_num [mixed_004_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_004]

def mixed_004_005 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(44963763/100000000), 0, (44660553/50000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (299807/50000000)]
    alternative := .zero
    polynomial := [(-118196758484062380454882503/13638867413506000000000000), (-44963763/599614), (-1134049225205749380454882503/6819433706753000000000000), (-44963763/599614), (-2149901691927436380454882503/13638867413506000000000000)]
    bernstein := [(849105692367450048538956633/3491550057857536000000000000), (9353509417523663953122568881/34915500578575360000000000000), (96006953498040728465674791801/349155005785753600000000000000), (924388624438164875952884605233/3491550057857536000000000000000), (8292203723430385849430763440217/34915500578575360000000000000000)]
    reserve := (59373369893/250000000000) }

theorem mixed_004_005_valid : mixed_004_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_005]
  · intro i; fin_cases i <;> norm_num [mixed_004_005]
  · norm_num [mixed_004_005]
  · norm_num [mixed_004_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_005]

def mixed_004_006 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1270743/3125000), 0, (22839737/25000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (37869/6250000)]
    alternative := .zero
    polynomial := [(-1491821400650989586193607/215342816412750000000000), (-847162/12623), (-17726648342564208336193607/107671408206375000000000), (-847162/12623), (-11320491761492475695397869/71780938804250000000000)]
    bernstein := [(8405256148349670730035914621/42405970001280000000000000000), (15366968137530188609686246297/68909701252080000000000000000), (114482691873073718952429187/496944960952500000000000000), (39590046990767363728989927/179452347010625000000000000), (502020682995166629483109/2588255004960937500000000)]
    reserve := (193961059491/1000000000000) }

theorem mixed_004_006_valid : mixed_004_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_006]
  · intro i; fin_cases i <;> norm_num [mixed_004_006]
  · norm_num [mixed_004_006]
  · norm_num [mixed_004_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_006]

def mixed_004_007 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7245283/20000000), 0, (93207547/100000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (611587/100000000)]
    alternative := .zero
    polynomial := [(-149908395024032739852459171/27822412434746000000000000), (-36226415/611587), (-2270014622482245739852459171/13911206217373000000000000), (-36226415/611587), (-4390120849940458739852459171/27822412434746000000000000)]
    bernstein := [(664678619972722964934400101/4347251942929062500000000000), (12364789713874393557032370839/69556031086865000000000000000), (154746509435791199922404866547/834672373042380000000000000000), (1567400964127936400042029193347/8903171979118720000000000000000), (10678312058515352934453169757629/71225375832949760000000000000000)]
    reserve := (149922860127/1000000000000) }

theorem mixed_004_007_valid : mixed_004_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_007]
  · intro i; fin_cases i <;> norm_num [mixed_004_007]
  · norm_num [mixed_004_007]
  · norm_num [mixed_004_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_007]

def mixed_004_008 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7915969/25000000), 0, (4742731/5000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (616623/100000000)]
    alternative := .zero
    polynomial := [(-28383922986601322088284407/7012877735608500000000000), (-31663876/616623), (-189258864331782107362761469/1168812955934750000000000), (-31663876/616623), (-1107169263004091322088284407/7012877735608500000000000)]
    bernstein := [(1923546670314704326214952201193/17952967003157760000000000000000), (1185601518101417258540009555597/8976483501578880000000000000000), (628052489254716785345585433713/4488241750789440000000000000000), (293839559059889977297067257877/2244120875394720000000000000000), (118110278314806629749696112633/1122060437697360000000000000000)]
    reserve := (52630978843/500000000000) }

theorem mixed_004_008_valid : mixed_004_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_008]
  · intro i; fin_cases i <;> norm_num [mixed_004_008]
  · norm_num [mixed_004_008]
  · norm_num [mixed_004_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_008]

def mixed_004_009 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(13494863/50000000), 0, (96288913/100000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (31049/5000000)]
    alternative := .zero
    polynomial := [(-256520803505416931307083/88280375858875000000000), (-13494863/310490), (-7100880872012063806307083/44140187929437500000000), (-13494863/310490), (-13945240940518710681307083/88280375858875000000000)]
    bernstein := [(859278346389710770269848677/14124860137420000000000000000), (484853562743085921800697639/5649944054968000000000000000), (636332975043539779155421991/6779932865961600000000000000), (15395700448460503810291123/180798209758976000000000000), (865669023315994859102973/14463856780718080000000000)]
    reserve := (29925248723/500000000000) }

theorem mixed_004_009_valid : mixed_004_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_009]
  · intro i; fin_cases i <;> norm_num [mixed_004_009]
  · norm_num [mixed_004_009]
  · norm_num [mixed_004_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_009]

def mixed_004_010 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(22218793/100000000), 0, (48750193/50000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (4997/800000)]
    alternative := .zero
    polynomial := [(-446272028351560331911579/227324313526000000000000), (-22218793/624625), (-957278099381237491153241/5982218777000000000000), (-22218793/624625), (-35930295748135464331911579/227324313526000000000000)]
    bernstein := [(515497600237075106943149/37244815528099840000000000), (9043030114791973697107313/232780097050624000000000000), (205278373321519089656744227/4364626819699200000000000000), (70131445258671204631372201/1818594508208000000000000000), (30801844227934270169982621/2273243135260000000000000000)]
    reserve := (13549735947/1000000000000) }

theorem mixed_004_010_valid : mixed_004_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_010]
  · intro i; fin_cases i <;> norm_num [mixed_004_010]
  · norm_num [mixed_004_010]
  · norm_num [mixed_004_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_010]

def mixed_004_011 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/10), (-7/80)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(1/100000000), (1/100000000), (1/100000000), 0, 0, 0, (99999997/100000000)]
    cone := fun i => (![![0, 0, (49098429/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(232333/1250000), 0, (39303/40000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (156637/50000000)]
    alternative := .zero
    polynomial := [(-985436931752387031072839223/356287757632300000000000000), (-464665986216657/7831850000000), (-56859756690866682812359339223/178143878816150000000000000), (-464665986216657/7831850000000), (-8671852034613921430280449171/27406750587100000000000000)]
    bernstein := [(10990314668734448770154086177/3562877576323000000000000000000), (443427708871574362470767450939/28503020610584000000000000000000), (13467291587934853754847471659119/684072494654016000000000000000000), (28287141140823086237115445654511/1824193319077376000000000000000000), (44386078060075490166204845279977/14593546552619008000000000000000000)]
    reserve := (3041486721/1000000000000) }

theorem mixed_004_011_valid : mixed_004_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_011]
  · intro i; fin_cases i <;> norm_num [mixed_004_011]
  · norm_num [mixed_004_011]
  · norm_num [mixed_004_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_011]

def mixed_004_012 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-7/80), (-3/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(15611293/100000000), (14607169/100000000), (1551771/20000000), (3059213/25000000), (3059213/25000000), (6978149/50000000), (23592681/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(3808667/100000000), 0, (582933/6250000), 0, 0]] i.1) i.2
    mu := ![(7148331/100000000), (14239/2000000), (4179309/100000000), (1830581/50000000), (1/100000000), (4690049/100000000), (14813/20000000)]
    alternative := .zero
    polynomial := [(-876983932864792501840192493305837323504469296817/1803336300330867436182698046311541900000000000000), (-92020425510197/7406500000000), (-70638532046228523335000706987265622697563007666817/901668150165433718091349023155770950000000000000), (-92020425510197/7406500000000), (-140400080159592254168161221481225408071621546036817/1803336300330867436182698046311541900000000000000)]
    bernstein := [(352019869119713984615896725865445070211386216481659983/73864654861552330186043311976920756224000000000000000000), (315526228517094652661473658387992935321880536288844907/36932327430776165093021655988460378112000000000000000000), (81298215978356234587320545639988768545035845611932787/7914070163737749662790354854670081024000000000000000000), (91968405361329415415264868646370237203619076232620787/9233081857694041273255413997115094528000000000000000000), (35146152231967237551265601303843358684336846091168223/4616540928847020636627706998557547264000000000000000000)]
    reserve := (297858859/62500000000) }

theorem mixed_004_012_valid : mixed_004_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_012]
  · intro i; fin_cases i <;> norm_num [mixed_004_012]
  · norm_num [mixed_004_012]
  · norm_num [mixed_004_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_012]

def mixed_004_013 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/40), (-1/16)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(48187/312500), (14587027/100000000), (1579331/20000000), (6322571/50000000), (6322571/50000000), (7236707/50000000), (1116639/5000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(3056311/100000000), 0, (1912311/25000000), 0, 0]] i.1) i.2
    mu := ![(6857479/100000000), (12093/2000000), (4191279/100000000), (235439/6250000), (1/100000000), (4856319/100000000), (14047/20000000)]
    alternative := .zero
    polynomial := [(-4088292637921835389454797214467228505187929087/12405143443242657974590399695942780000000000000), (-7030496085727/702350000000), (-463474990161744255538094728664664419818986809087/6202571721621328987295199847971390000000000000), (-7030496085727/702350000000), (-922861687685566675686734660114861611132785689087/12405143443242657974590399695942780000000000000)]
    bernstein := [(86848655363770870991802256090838305197978162758353/31757167214701204414951423221613516800000000000000000), (80593450390876818060527425784545397302718466147931/12702866885880481765980569288645406720000000000000000), (121971896382442466284569436831612989857727497425243/15243440263056578119176683146374488064000000000000000), (15674430989008568017582564889500157935405354924163/2032458701740877082556891086183265075200000000000000), (4455203884083753836493668506546073260025642612737/812983480696350833022756434473306030080000000000000)]
    reserve := (1367386687/500000000000) }

theorem mixed_004_013_valid : mixed_004_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_013]
  · intro i; fin_cases i <;> norm_num [mixed_004_013]
  · norm_num [mixed_004_013]
  · norm_num [mixed_004_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_013]

def mixed_004_014 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/16), (-1/20)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(609159/4000000), (14560681/100000000), (8023287/100000000), (407303/3125000), (407303/3125000), (14967559/100000000), (10576053/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1186053/50000000), 0, (1512779/25000000), 0, 0]] i.1) i.2
    mu := ![(6585857/100000000), (124717/25000000), (2100387/50000000), (60427/1562500), (1/100000000), (5014951/100000000), (66621/100000000)]
    alternative := .zero
    polynomial := [(-38857200290471124408984600516974223986216647627/185756866526463264658831719142293072000000000000), (-8685855302173/1110350000000), (-6649855603638037290069460743295763301082984147627/92878433263231632329415859571146536000000000000), (-8685855302173/1110350000000), (-13260854006985603455729936886074552378179751647627/185756866526463264658831719142293072000000000000)]
    bernstein := [(10643236742830137392153921996342720408474899804277/12173762004678296512681195545709318766592000000000000), (21951775617777418568403030276329889364734178225127/5072400835282623546950498144045549486080000000000000), (337320339757259102073494592882503038765218129676847/57064509396929514903193104120512431718400000000000000), (44619177832178815782260003222816503573419102948311/7925626305129099292110153350071171072000000000000000), (103620081867765862820113236496062515978456753130773/29721098644234122345413075062766891520000000000000000)]
    reserve := (437138361/500000000000) }

theorem mixed_004_014_valid : mixed_004_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_014]
  · intro i; fin_cases i <;> norm_num [mixed_004_014]
  · norm_num [mixed_004_014]
  · norm_num [mixed_004_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_014]

def mixed_004_015 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/20), (-7/160)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(7563347/50000000), (2915049/20000000), (8111369/100000000), (13278577/100000000), (13278577/100000000), (1526041/10000000), (20369129/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1905419/100000000), 0, (5019403/100000000), 0, 0]] i.1) i.2
    mu := ![(6410897/100000000), (39979/10000000), (526847/12500000), (61433/1562500), (1/100000000), (5111391/100000000), (16051/50000000)]
    alternative := .zero
    polynomial := [(-7622344728102220391403101563551055151218176517/27223135931628938918848913446105320000000000000), (-39747514440031/3210200000000), (-262028071227854221417931243221777416838896210931/1944509709402067065632065246150380000000000000), (-39747514440031/3210200000000), (-3660770652461856879459634303541332780593328776517/27223135931628938918848913446105320000000000000)]
    bernstein := [(12682977686398267810597533437928979562376339289883/4355701749060630227015826151376851200000000000000000), (53204499065115765217934610335731473749906438234127/11615204664161680605375536403671603200000000000000000), (4491767243568303681739975454829939420929190423120401/836294735819641003587038621064355430400000000000000000), (3928002166299625760287138037121645560823253011434223/743373098506347558744034329834982604800000000000000000), (77077305669952696414751682652119261059246992388613083/17840954364152341409856823916039582515200000000000000000)]
    reserve := (2911810407/1000000000000) }

theorem mixed_004_015_valid : mixed_004_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_015]
  · intro i; fin_cases i <;> norm_num [mixed_004_015]
  · norm_num [mixed_004_015]
  · norm_num [mixed_004_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_015]

def mixed_004_016 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-7/160), (-3/80)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(1879201/12500000), (1819999/12500000), (8167499/100000000), (6728973/50000000), (6728973/50000000), (3097867/20000000), (793347/4000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1608831/100000000), 0, (4278981/100000000), 0, 0]] i.1) i.2
    mu := ![(1257711/20000000), (348019/100000000), (4218329/100000000), (3977799/100000000), (1/100000000), (5184781/100000000), (1251/4000000)]
    alternative := .zero
    polynomial := [(-3716360713076328269535148480265975071331987/18155126044082441645741876331420000000000000), (-145865594149/13900000000), (-1198817094568297439477764489957645758682931987/9077563022041220822870938165710000000000000), (-145865594149/13900000000), (-341988261203359792955141975919289363184933141/2593589434868920235105982333060000000000000)]
    bernstein := [(1854621115971169512769470148621865501910338107201/915241800326912996688722774812262400000000000000000), (1674920676553256444480529276784733688274303689829/457620900163456498344361387406131200000000000000000), (5651280346083050517656918566264947207826383227257/1274801079026771673959292436345651200000000000000000), (29248443500247719689201311759391582013168445517/6729719120050830858005314520678400000000000000000), (11440207858932717108219876671741188175622364193/3364859560025415429002657260339200000000000000000)]
    reserve := (506593207/250000000000) }

theorem mixed_004_016_valid : mixed_004_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_016]
  · intro i; fin_cases i <;> norm_num [mixed_004_016]
  · norm_num [mixed_004_016]
  · norm_num [mixed_004_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_016]

def mixed_004_017 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/80), (-1/32)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(7470839/50000000), (14544441/100000000), (2055337/25000000), (13632307/100000000), (13632307/100000000), (15712187/100000000), (19315733/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1326389/100000000), 0, (3557951/100000000), 0, 0]] i.1) i.2
    mu := ![(6170523/100000000), (296671/100000000), (2110791/50000000), (4022539/100000000), (1/100000000), (1051237/20000000), (3809/12500000)]
    alternative := .zero
    polynomial := [(-98712753420903159287981931006116773426017410373/691531025620428890588966182668802900000000000000), (-26506572190441/3047200000000), (-44866936694414507666799968470673261103735598035373/345765512810214445294483091334401450000000000000), (-26506572190441/3047200000000), (-89635160635408112174311955010340405434045178660373/691531025620428890588966182668802900000000000000)]
    bernstein := [(2572059075648507660970021128413013518936267665035399/2178854677647135950655696526316474368000000000000000000), (2863995788881832553805336020613239236285071690480219/1030004029433191540309965630622333337600000000000000000), (48063720140736191409347186338553064013854958706648201/13596053188518128332091546324214800056320000000000000000), (22708117172033533003100865900417112403041666596731/6592025788372425857983780035982933360640000000000000), (224008440063701383303237621074407780742501420999/89245887596426688538857329717922790113280000000000)]
    reserve := (1180463801/1000000000000) }

theorem mixed_004_017_valid : mixed_004_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_017]
  · intro i; fin_cases i <;> norm_num [mixed_004_017]
  · norm_num [mixed_004_017]
  · norm_num [mixed_004_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_017]

def mixed_004_018 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/32), (-1/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(2970217/20000000), (14528839/100000000), (8273029/100000000), (6900833/50000000), (6900833/50000000), (7964463/50000000), (1881479/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(211499/20000000), 0, (1428061/50000000), 0, 0]] i.1) i.2
    mu := ![(378543/6250000), (122873/50000000), (4224597/100000000), (4065943/100000000), (1/100000000), (5325597/100000000), (29693/100000000)]
    alternative := .zero
    polynomial := [(-6885948139755268059915489043502233644196834769/73882999916069053821222550871331900000000000000), (-648729874497/92790625000), (-163048172253272254609439264325042276994973727061/1273844826139121617607285359850550000000000000), (-648729874497/92790625000), (-9449908042550035499287561841808949832064279334769/73882999916069053821222550871331900000000000000)]
    bernstein := [(46206666528461959585508668092531874981256813311/123955104831987238687427612003932349399040000000000), (358013379947478024824610494900436193319810622731/184457001238076248046767279767756472320000000000000), (971466946025632682404010216567108433763311512955757/363149721187462613342073082042770554880000000000000000), (18560611419246938637637240529342689348669983124691/7205351610862353439326846865927987200000000000000000), (310901554894455030170833049941467472863342120764431/189140479785136777782329730230609664000000000000000000)]
    reserve := (372769371/1000000000000) }

theorem mixed_004_018_valid : mixed_004_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_018]
  · intro i; fin_cases i <;> norm_num [mixed_004_018]
  · norm_num [mixed_004_018]
  · norm_num [mixed_004_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_018]

def mixed_004_019 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/40), (-7/320)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14784117/100000000), (2903449/20000000), (2077609/25000000), (3481353/25000000), (3481353/25000000), (321749/2000000), (18449929/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(432183/50000000), 0, (2342221/100000000), 0, 0]] i.1) i.2
    mu := ![(5973999/100000000), (24617/12500000), (4226739/100000000), (4097629/100000000), (1/100000000), (2688173/50000000), (7281/50000000)]
    alternative := .zero
    polynomial := [(-1405640967233567369400157614404881938733153783/11078324167449478846203996152184522000000000000), (-2728381928899/242700000000), (-1355179858185706371647220263989118983713591605033/5539162083724739423101998076092261000000000000), (-2728381928899/242700000000), (-300994897267131019547226707818203676165383339587/1230924907494386538467110683576058000000000000)]
    bernstein := [(37827163701022990449738098406322273785741654958117/28360509868670665846282230149592376320000000000000000), (477235098341920998944117122474076044641043043574019/226884078949365326770257841196739010560000000000000000), (13475527064742377927779496216522687297292134369772799/5445217894784767842486188188721736253440000000000000000), (35544049003581045768244827512353833219544913389182931/14520581052759380913296501836591296675840000000000000000), (234976813758357722604307655394660031137416875204022917/116164648422075047306372014692730373406720000000000000000)]
    reserve := (53351881/40000000000) }

theorem mixed_004_019_valid : mixed_004_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_019]
  · intro i; fin_cases i <;> norm_num [mixed_004_019]
  · norm_num [mixed_004_019]
  · norm_num [mixed_004_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_019]

def mixed_004_020 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-7/320), (-3/160)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14739971/100000000), (725481/5000000), (1666951/20000000), (2801271/20000000), (2801271/20000000), (16191209/100000000), (9105867/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(739547/100000000), 0, (2005503/100000000), 0, 0]] i.1) i.2
    mu := ![(2960063/50000000), (171791/100000000), (1057031/25000000), (514793/12500000), (1/100000000), (1081911/20000000), (1797/12500000)]
    alternative := .zero
    polynomial := [(-1686316401254300643710111252856870585613515839/17932468555989312210187369251827100000000000000), (-2314268973123/239600000000), (-2180196181698430651761574496762635016215432515839/8966234277994656105093684625913550000000000000), (-2314268973123/239600000000), (-4358706046995607002879438882272413161845251515839/17932468555989312210187369251827100000000000000)]
    bernstein := [(177212693387552631901075425139890547746416522690297761/188035561485650490401094309006038532096000000000000000000), (160259135541566712567450479124417680735971823166812869/94017780742825245200547154503019266048000000000000000000), (292040176320621442907415062680073617101073064154029803/141026671114237867800820731754528899072000000000000000000), (47979404968760259881723020592782028003355119965768829/23504445185706311300136788625754816512000000000000000000), (18992223792143177874208855371562786564185971441565841/11752222592853155650068394312877408256000000000000000000)]
    reserve := (23561061/25000000000) }

theorem mixed_004_020_valid : mixed_004_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_020]
  · intro i; fin_cases i <;> norm_num [mixed_004_020]
  · norm_num [mixed_004_020]
  · norm_num [mixed_004_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_020]

def mixed_004_021 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/160), (-1/64)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14696247/100000000), (1450211/10000000), (8358597/100000000), (14086059/100000000), (14086059/100000000), (16293427/100000000), (17977501/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(308897/50000000), 0, (334691/20000000), 0, 0]] i.1) i.2
    mu := ![(146681/2500000), (146749/100000000), (1057371/25000000), (827747/20000000), (1/100000000), (1088453/20000000), (887/6250000)]
    alternative := .zero
    polynomial := [(-3555934107799342507424605010924424677284999/53496874131469710714003185659950000000000000), (-5759010071517/709600000000), (-6479779493247228095904050331994715929693441249/26748437065734855357001592829975000000000000), (-5759010071517/709600000000), (-12956003052386656849300676058978507434709597499/53496874131469710714003185659950000000000000)]
    bernstein := [(19642501740008557258495031599996142305297280423381/35059711430799989613529127754104832000000000000000000), (18444000152520771039763626749685988855920830080487/14023884572319995845411651101641932800000000000000000), (4028631003405155842203035460698761703409514797953/2404094498111999287784854474567188480000000000000000), (3684338856454136902904810894690766789575047793071/2243821531571199335265864176262709248000000000000000), (1089603987595284459823954757418018186170989907909/897528612628479734106345670505083699200000000000000)]
    reserve := (560258511/1000000000000) }

theorem mixed_004_021_valid : mixed_004_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_021]
  · intro i; fin_cases i <;> norm_num [mixed_004_021]
  · norm_num [mixed_004_021]
  · norm_num [mixed_004_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_021]

def mixed_004_022 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/64), (-1/80)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14652961/100000000), (14494741/100000000), (8381973/100000000), (885283/6250000), (885283/6250000), (16394103/100000000), (8873583/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(3119/625000), 0, (269209/20000000), 0, 0]] i.1) i.2
    mu := ![(2907663/50000000), (121811/100000000), (169233/4000000), (1039701/25000000), (1/100000000), (5474477/100000000), (3503/25000000)]
    alternative := .zero
    polynomial := [(-584002059797546073223115446840044904203671513/13278968997377823344834624443577100000000000000), (-1157843292803/175150000000), (-1608184654333984934195217102984996997631681171513/6639484498688911672417312221788550000000000000), (-1157843292803/175150000000), (-3215785306608172322317211090523153950359158671513/13278968997377823344834624443577100000000000000)]
    bernstein := [(2451262821732546865131743699392057224395885508599/13104948889783010345066645798163107020800000000000000), (5105991637325932942501230718616697508685530281469/5460395370742920977111102415901294592000000000000000), (1345935254130733489563126198610002572461795936037173/1044300614654583636872498337041122590720000000000000000), (181061942987606946308745841591954365874645466504909/145041752035358838454513657922378137600000000000000000), (10793914015706376114316073943109253211887317889807/13266013905673064492790883346558976000000000000000000)]
    reserve := (46762159/250000000000) }

theorem mixed_004_022_valid : mixed_004_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_022]
  · intro i; fin_cases i <;> norm_num [mixed_004_022]
  · norm_num [mixed_004_022]
  · norm_num [mixed_004_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_022]

def mixed_004_023 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/80), (-7/640)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14620793/100000000), (7244661/50000000), (8399209/100000000), (14222571/100000000), (14222571/100000000), (8234299/50000000), (3515387/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(411903/100000000), 0, (110351/10000000), 0, 0]] i.1) i.2
    mu := ![(288851/5000000), (48877/50000000), (2115911/50000000), (834729/20000000), (1/100000000), (5498309/100000000), (6939/100000000)]
    alternative := .zero
    polynomial := [(-2535520344750511699035098276610243781145143/41947327404673345506102251582225000000000000), (-826786118669/77100000000), (-264403131528703697875973038059777112959541793861/566288919963090164332380396360037500000000000), (-826786118669/77100000000), (-528737804008099131936072128466085749336992668861/1132577839926180328664760792720075000000000000)]
    bernstein := [(820915133307814164819986378842666864819725387847/1253794279010171520597529785670656000000000000000000), (380377513357371165976171177964484800181152433181973/371123106587010770096868816558514176000000000000000000), (1533432958611431301791343258378035909465600384107519/1272422079726894068903550228200620032000000000000000000), (28391465235588688180977713472643333443947853494124677/23751878821568689286199604259744907264000000000000000000), (189172244958021862899511332330639051313245191836675939/190015030572549514289596834077959258112000000000000000000)]
    reserve := (654744679/1000000000000) }

theorem mixed_004_023_valid : mixed_004_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_023]
  · intro i; fin_cases i <;> norm_num [mixed_004_023]
  · norm_num [mixed_004_023]
  · norm_num [mixed_004_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_023]

def mixed_004_024 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-7/640), (-3/320)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(3649873/25000000), (14485767/100000000), (4205281/50000000), (14260883/100000000), (14260883/100000000), (825889/5000000), (17464633/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(177357/50000000), 0, (943251/100000000), 0, 0]] i.1) i.2
    mu := ![(5751779/100000000), (1067/1250000), (846497/20000000), (4183441/100000000), (1/100000000), (2757021/50000000), (1379/20000000)]
    alternative := .zero
    polynomial := [(-111047498525865660559069634620888150152979/2462847367778805005122935883380000000000000), (-1598677139223/172375000000), (-575251631590368033909942666701012376278397979/1231423683889402502561467941690000000000000), (-1598677139223/172375000000), (-1150392215682210202159326263767403864406642979/2462847367778805005122935883380000000000000)]
    bernstein := [(194786403508420229157606440564225629739088239724221/413197222642564517928286018696170700800000000000000000), (173533443847775897101221780148005405511997797027409/206598611321282258964143009348085350400000000000000000), (315600858586916704178803845501714201703389280509983/309897916981923388446214514022128025600000000000000000), (51999196610038106120200772361442471593289428662569/51649652830320564741035752337021337600000000000000000), (20790463731716064241122474552874957769448575185901/25824826415160282370517876168510668800000000000000000)]
    reserve := (58926583/125000000000) }

theorem mixed_004_024_valid : mixed_004_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_024]
  · intro i; fin_cases i <;> norm_num [mixed_004_024]
  · norm_num [mixed_004_024]
  · norm_num [mixed_004_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_024]

def mixed_004_025 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/320), (-1/128)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(1457831/10000000), (14482261/100000000), (1684361/20000000), (1787361/12500000), (1787361/12500000), (1035411/6250000), (17353271/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(298237/100000000), 0, (196033/25000000), 0, 0]] i.1) i.2
    mu := ![(2863387/50000000), (72991/100000000), (2116573/50000000), (1048289/25000000), (1/100000000), (110593/2000000), (6851/100000000)]
    alternative := .zero
    polynomial := [(-563470057729572978879429786798644141741496441/17567714054796946885369452192615350000000000000), (-413371032573/52700000000), (-4115015122054750809353786710548113160994977996441/8783857027398473442684726096307675000000000000), (-413371032573/52700000000), (-8229466774051772045728693991309427677848214496441/17567714054796946885369452192615350000000000000)]
    bernstein := [(53465944815252829283029334182496238572870572165577079/184210833327227633772731587023238332416000000000000000000), (120170364453983225602197318634532325162916219448751/182839536801218495059783212926291148800000000000000000), (664045679473518304718990577292990295684120476618707/796587387360984362260460916857246842880000000000000000), (148612348506864868445265019140772423557826952518293/181376820506808747099304947222880819609600000000000000), (115911060615432265645427421323938314686880522236511/188631893327081096983277145111796052393984000000000000)]
    reserve := (18140201/62500000000) }

theorem mixed_004_025_valid : mixed_004_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_025]
  · intro i; fin_cases i <;> norm_num [mixed_004_025]
  · norm_num [mixed_004_025]
  · norm_num [mixed_004_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_025]

def mixed_004_026 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/128), (-1/160)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(227457/1562500), (1809851/12500000), (8432943/100000000), (14336587/100000000), (14336587/100000000), (16614987/100000000), (431071/2500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(48493/20000000), 0, (156537/25000000), 0, 0]] i.1) i.2
    mu := ![(5702003/100000000), (7581/12500000), (4233807/100000000), (4202793/100000000), (1/100000000), (1109027/20000000), (851/12500000)]
    alternative := .zero
    polynomial := [(-221659130396583819646165348343490836743849/10380807706894417249032163637700000000000000), (-547241081291/85100000000), (-349586843999897281077521042720627442247463407/741486264778172660645154545550000000000000), (-547241081291/85100000000), (-4893994156868165351265648432740440700627743849/10380807706894417249032163637700000000000000)]
    bernstein := [(12395817813069694542595342102822588372380172079/111463074017940689523928576190104731648000000000000), (110713618695854353351536483615152699817042407929/232214737537376436508184533729384857600000000000000), (8496692135123067722082076851552801049118868073157/13062078986477424553585380022277898240000000000000000), (1147207162478242360345048379862445947405578394077/1814177637010753410220191669760819200000000000000000), (410513844514651920319204977611103186101818078193/971880876970046469760816965943296000000000000000000)]
    reserve := (111210083/1000000000000) }

theorem mixed_004_026_valid : mixed_004_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_026]
  · intro i; fin_cases i <;> norm_num [mixed_004_026]
  · norm_num [mixed_004_026]
  · norm_num [mixed_004_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_026]

def mixed_004_027 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/160), (-7/1280)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14541531/100000000), (7238127/50000000), (4220613/50000000), (14364661/100000000), (14364661/100000000), (16651043/100000000), (1072539/6250000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(100547/50000000), 0, (508403/100000000), 0, 0]] i.1) i.2
    mu := ![(5683577/100000000), (761/1562500), (66161/1562500), (4209969/100000000), (1/100000000), (5556667/100000000), (847/25000000)]
    alternative := .zero
    polynomial := [(-66877027632672295281348251078414643184609169/2268010894758587720727625338190800000000000000), (-44362370247/4235000000), (-1034697257612397085031817325853288673589329671669/1134005447379293860363812669095400000000000000), (-44362370247/4235000000), (-2069327638197161497768353303455498932535474734169/2268010894758587720727625338190800000000000000)]
    bernstein := [(508706501638617421092018726655196836206905939973031/1486363619988988048656056541636722688000000000000000000), (2076373149490342299613656630859989459492787796414939/3963636319970634796416150777697927168000000000000000000), (174837329309378468879161128178916248901255894590000357/285381815037885705341962855994250756096000000000000000000), (154388849407557207769601943182545092958206318775308011/253672724478120626970633649772667338752000000000000000000), (3115724121954295864221062005893834607148321050478639431/6088145387474895047295207594544016130048000000000000000000)]
    reserve := (171124513/500000000000) }

theorem mixed_004_027_valid : mixed_004_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_027]
  · intro i; fin_cases i <;> norm_num [mixed_004_027]
  · norm_num [mixed_004_027]
  · norm_num [mixed_004_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_027]

def mixed_004_028 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-7/1280), (-3/640)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14531091/100000000), (14474569/100000000), (2111679/25000000), (7191641/50000000), (7191641/50000000), (208437/1250000), (171061/1000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(173729/100000000), 0, (215129/50000000), 0, 0]] i.1) i.2
    mu := ![(1134273/20000000), (851/2000000), (846927/20000000), (4214729/100000000), (1/100000000), (1391079/25000000), (3377/100000000)]
    alternative := .zero
    polynomial := [(-396799706161939782379080651939183689175583/17984697354462237425676156490830000000000000), (-139526676633/15350000000), (-8236413775580404349453545243504874370225882583/8992348677231118712838078245415000000000000), (-139526676633/15350000000), (-16472430751454646759124711406357809556762589583/17984697354462237425676156490830000000000000)]
    bernstein := [(12243267471397144817503161813104270178614304379185617/48277304353670643381416451759433108684800000000000000000), (34193647044540369285368398148066403187236473777399/78627531520636227005564253679858483200000000000000000), (18936207156998227156800355368214772541680197677431291/36207978265252982536062338819574831513600000000000000000), (3125432654785336374996627733197544629154028750133613/6034663044208830422677056469929138585600000000000000000), (1266281305919262339887756839402416093182266065021377/3017331522104415211338528234964569292800000000000000000)]
    reserve := (253602963/1000000000000) }

theorem mixed_004_028_valid : mixed_004_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_028]
  · intro i; fin_cases i <;> norm_num [mixed_004_028]
  · norm_num [mixed_004_028]
  · norm_num [mixed_004_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_028]

def mixed_004_029 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/640), (-1/256)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(7260341/50000000), (14472899/100000000), (422609/5000000), (14401827/100000000), (14401827/100000000), (834939/5000000), (3410361/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(18317/12500000), 0, (70479/20000000), 0, 0]] i.1) i.2
    mu := ![(565921/10000000), (18201/50000000), (2117483/50000000), (4219469/100000000), (1/100000000), (2785967/50000000), (3367/100000000)]
    alternative := .zero
    polynomial := [(-67917636803579555015961919167427737626474717/4316362203743943130707964917834315000000000000), (-99852453821/12950000000), (-1988336047896846238151607432741535352682598774717/2158181101871971565353982458917157500000000000), (-99852453821/12950000000), (-1325534726052296298916066301187967759209190358239/1438787401247981043569321639278105000000000000)]
    bernstein := [(119835791792814836011574999763737217958290754846730323/724165410264481425956037603469285549670400000000000000000), (100349244870279468013896763073405207244233624836145521/289666164105792570382415041387714219868160000000000000000), (21534235592949845077040608011030899442533972149719239/49657056703850154922699721380751009120256000000000000000), (6599255211685713198974850296062773898048350401514851/15448862085642270420395468874011425059635200000000000000), (6061341342212569341147336032113914531902304741763427/18538634502770724504474562648813710071562240000000000000)]
    reserve := (82740621/500000000000) }

theorem mixed_004_029_valid : mixed_004_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_029]
  · intro i; fin_cases i <;> norm_num [mixed_004_029]
  · norm_num [mixed_004_029]
  · norm_num [mixed_004_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_029]

def mixed_004_030 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/256), (-1/320)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(453447/3125000), (2894249/20000000), (8457619/100000000), (2884059/20000000), (2884059/20000000), (2090313/12500000), (16997737/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(59757/50000000), 0, (274813/100000000), 0, 0]] i.1) i.2
    mu := ![(5647113/100000000), (30261/100000000), (4235299/100000000), (4224189/100000000), (1/100000000), (2789761/50000000), (839/25000000)]
    alternative := .zero
    polynomial := [(-5092058465737013555501951350500647379568993/484819157712863886135545429432325000000000000), (-1064299268129/167800000000), (-225514857733824436553912406585167175394504037743/242409578856431943067772714716162500000000000), (-1064299268129/167800000000), (-451024623409183136094269311218983850141628506493/484819157712863886135545429432325000000000000)]
    bernstein := [(162134720076228735580534792540610856611664857790083/2082282426851016549451635442534111720243200000000000000), (224349941356843184934646657593685951390201613248513/867617677854590228938181434389213216768000000000000000), (3364147556874711947735149250910874824071780752260233/9760698875864140075554541136878648688640000000000000000), (35049660080145392459319054650464021936462348127173/104280970895984402516608345479472742400000000000000000), (91083528476526795092547299692724404983727409388239/391053640859941509437281295548022784000000000000000000)]
    reserve := (38931971/500000000000) }

theorem mixed_004_030_valid : mixed_004_030.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_030]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_030]
  · intro i; fin_cases i <;> norm_num [mixed_004_030]
  · norm_num [mixed_004_030]
  · norm_num [mixed_004_030, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_030, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_030, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_030, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_030]

def mixed_004_031 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/320), (-7/2560)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14502541/100000000), (7235007/50000000), (8461681/100000000), (14434097/100000000), (14434097/100000000), (8370117/50000000), (3391467/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(99359/100000000), 0, (216809/100000000), 0, 0]] i.1) i.2
    mu := ![(5638077/100000000), (24309/100000000), (1058887/25000000), (4227717/100000000), (1/100000000), (698149/12500000), (837/50000000)]
    alternative := .zero
    polynomial := [(-1073135539447733533680853669269365170226359/73771893431094865449745625198850000000000000), (-577769818379/55800000000), (-66545034340419128225890649341152120397488851359/36885946715547432724872812599425000000000000), (-577769818379/55800000000), (-133088995545298808718247617828634971429807476359/73771893431094865449745625198850000000000000)]
    bernstein := [(11468084370370727545728173403736633645202572796957/59504182251079792026024975914237952000000000000000000), (44854677686570378011976385365425962396302644551833/158677819336212778736066602437967872000000000000000000), (48529373908323430465039427344120487138956294338236027/148522438898695160896958339881937928192000000000000000000), (42898268766413044036186422298116762836018607035261621/132019945687729031908407413228389269504000000000000000000), (878454067849506314867685196829303250014147399635066841/3168478696505496765801777917481342468096000000000000000000)]
    reserve := (96363683/500000000000) }

theorem mixed_004_031_valid : mixed_004_031.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_031]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_031]
  · intro i; fin_cases i <;> norm_num [mixed_004_031]
  · norm_num [mixed_004_031]
  · norm_num [mixed_004_031, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_031, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_031, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_031, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_031]

def mixed_004_032 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-7/2560), (-3/1280)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(453043/3125000), (7234599/50000000), (4232191/50000000), (577731/4000000), (577731/4000000), (2094003/12500000), (16930471/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(42987/50000000), 0, (44557/25000000), 0, 0]] i.1) i.2
    mu := ![(5632071/100000000), (21243/100000000), (847143/20000000), (2115031/50000000), (1/100000000), (5588963/100000000), (209/12500000)]
    alternative := .zero
    polynomial := [(-1715141280438125801033734950185072615693/157490448230054590860152731950000000000000), (-751982655933/83600000000), (-114646970101260183825043990210020164249944526479/63232414964366918230351321877925000000000000), (-751982655933/83600000000), (-229292562944072175835069750330875329886578651479/126464829928733836460702643755850000000000000)]
    bernstein := [(810016290424889899761769045723829002264434421578067721/5431623086381138382873302441121143586816000000000000000000), (649100559643861861814932373606039756553372091072472909/2715811543190569191436651220560571793408000000000000000000), (1151951083147689033568196132138732356900181793445232483/4073717314785853787154976830840857690112000000000000000000), (190402267770880936899414965028407162313626522581840069/678952885797642297859162805140142948352000000000000000000), (78753241307507485182576495740869316132612924717505401/339476442898821148929581402570071474176000000000000000000)]
    reserve := (74564847/500000000000) }

theorem mixed_004_032_valid : mixed_004_032.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_032]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_032]
  · intro i; fin_cases i <;> norm_num [mixed_004_032]
  · norm_num [mixed_004_032]
  · norm_num [mixed_004_032, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_032, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_032, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_032, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_032]

def mixed_004_033 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/1280), (-1/512)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14492219/100000000), (7234193/50000000), (2116769/25000000), (14452433/100000000), (14452433/100000000), (1676379/10000000), (16903663/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(72633/100000000), 0, (139717/100000000), 0, 0]] i.1) i.2
    mu := ![(5626079/100000000), (9089/50000000), (2117941/50000000), (4232403/100000000), (1/100000000), (223709/4000000), (1669/100000000)]
    alternative := .zero
    polynomial := [(-475284773128358905499089992107554992741559/61122986031929303969010010581097500000000000), (-1276059227147/166900000000), (-55846653170173302251293292994541125043205091559/30561493015964651984505005290548750000000000), (-1276059227147/166900000000), (-111692831055573476143681086899090142531417441559/61122986031929303969010010581097500000000000)]
    bernstein := [(17344407478981527714283555525833921577697488291412921/164075766275625732706838120589017323929600000000000000000), (12834469696563726336241012167897838583218403714508947/65630306510250293082735248235606929571840000000000000000), (2688204637587797601998672602527565689585408501145109/11250909687471478814183185411818330783744000000000000000), (495294218765177570634382538380685532288620876572607/2100169808328009378647527943539421746298880000000000000), (31295303762984443210900477640579854400331182816081/168013584666240750291802235483153739703910400000000000)]
    reserve := (21141949/200000000000) }

theorem mixed_004_033_valid : mixed_004_033.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_033]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_033]
  · intro i; fin_cases i <;> norm_num [mixed_004_033]
  · norm_num [mixed_004_033]
  · norm_num [mixed_004_033, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_033, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_033, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_033, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_033]

def mixed_004_034 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/512), (-1/640)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14487069/100000000), (14467579/100000000), (8469763/100000000), (3615393/25000000), (3615393/25000000), (4193883/25000000), (1054807/6250000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(59333/100000000), 0, (4051/4000000), 0, 0]] i.1) i.2
    mu := ![(2810051/50000000), (3023/20000000), (4236049/100000000), (4234739/100000000), (1/100000000), (17489/312500), (833/50000000)]
    alternative := .zero
    polynomial := [(-576234959967591049823302334825440767193901/110999227525241855937026979975550000000000000), (-262390948231/41650000000), (-102581601417046261221758514428868848935113543901/55499613762620927968513489987775000000000000), (-262390948231/41650000000), (-205162626599132554852467205555402872429459893901/110999227525241855937026979975550000000000000)]
    bernstein := [(19025600191955688995510459624007327370441821790059/305112353345393142873519561257365842952192000000000000), (290259965370962963688058008067841012076557220201751/1906952208408707142959497257858536518451200000000000000), (6974484318955022661521332823371314357897238035539033/35755353907663258930490573584847559720960000000000000000), (2844123651782040349118224119335219480913579231848819/14898064128193024554371072327019816550400000000000000000), (153082551623320063154281918804714964258073827073347/1095445891778898864291990612280868864000000000000000000)]
    reserve := (31178023/500000000000) }

theorem mixed_004_034_valid : mixed_004_034.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_034]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_034]
  · intro i; fin_cases i <;> norm_num [mixed_004_034]
  · norm_num [mixed_004_034]
  · norm_num [mixed_004_034, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_034, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_034, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_034, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_034]

def mixed_004_035 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/640), (-3/2560)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(1810241/12500000), (578671/4000000), (1694489/20000000), (14470693/100000000), (14470693/100000000), (67149/400000), (2106277/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1843/4000000), 0, (62903/100000000), 0, 0]] i.1) i.2
    mu := ![(2807069/50000000), (6027/50000000), (529527/12500000), (423707/10000000), (1/100000000), (1400057/25000000), (13/781250)]
    alternative := .zero
    polynomial := [(-88801165159195720923130295228482025593/28343434400183727925835741328000000000000), (-4122595647/832000000), (-115459350300347474331843465889062293448065903/61410774533731410505977439544000000000000), (-4122595647/832000000), (-14137856069121179111156914176337465110654341/7519686677599764551752339536000000000000)]
    bernstein := [(393462879750711068560935785902526856367797761497/20606036581594223200869055887132590080000000000000000), (26944936855199349440063769962668701873009256807073/247272438979130678410428670645591080960000000000000000), (1214479822912092259698776000608975195937379072953/8041380129402623688144021809612718080000000000000000), (574760523114465116225076668065914406680536737209257/3956359023666090854566858730329457295360000000000000000), (1451314271412996426141829654045103806524126341637371/15825436094664363418267434921317829181440000000000000000)]
    reserve := (1193409/62500000000) }

theorem mixed_004_035_valid : mixed_004_035.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_035]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_035]
  · intro i; fin_cases i <;> norm_num [mixed_004_035]
  · norm_num [mixed_004_035]
  · norm_num [mixed_004_035, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_035, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_035, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_035, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_035]

def mixed_004_036 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/2560), (-1/1024)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14478077/100000000), (578647/4000000), (2118613/25000000), (14477521/100000000), (14477521/100000000), (16796023/100000000), (16830231/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(36159/100000000), 0, (3417/10000000), 0, 0]] i.1) i.2
    mu := ![(224387/4000000), (9083/100000000), (4236341/100000000), (847763/20000000), (1/100000000), (5603033/100000000), (831/100000000)]
    alternative := .zero
    polynomial := [(-422922944540963362010832275572830123014987/109939785621924714080330924691900000000000000), (-210869035193/27700000000), (-200047065942842414928670787424958473952794014987/54969892810962357040165462345950000000000000), (-210869035193/27700000000), (-400093708962740288893979564017641375075465014987/109939785621924714080330924691900000000000000)]
    bernstein := [(361060165955455194442704715839595512675417147063808453/4721877837754176675491720384091493761024000000000000000000), (228974588534749138450370525148333688461238848531886231/1888751135101670670196688153636597504409600000000000000000), (323788948325324684829552541968360295353309028115730583/2266501362122004804236025784363917005291520000000000000000), (42715632771778752718412810811920677554780859418710943/302200181616267307231470104581855600705536000000000000000), (14106902747028297329180835351310266267950752211489077/120880072646506922892588041832742240282214400000000000000)]
    reserve := (2389543/31250000000) }

theorem mixed_004_036_valid : mixed_004_036.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_036]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_036]
  · intro i; fin_cases i <;> norm_num [mixed_004_036]
  · norm_num [mixed_004_036]
  · norm_num [mixed_004_036, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_036, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_036, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_036, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_036]

def mixed_004_037 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/1024), (-1/1280)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(1809439/12500000), (904111/6250000), (2118947/25000000), (14482067/100000000), (14482067/100000000), (2100233/12500000), (8408463/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(29561/100000000), 0, (3759/25000000), 0, 0]] i.1) i.2
    mu := ![(350419/6250000), (3777/50000000), (169457/4000000), (4239977/100000000), (1/100000000), (5604901/100000000), (83/10000000)]
    alternative := .zero
    polynomial := [(-56689218018567737627433115113057276421067/22119417594254484670069098469050000000000000), (-260569168823/41500000000), (-40749947140762149955355167395704592008513421067/11059708797127242335034549234525000000000000), (-260569168823/41500000000), (-27166612530768760447657569119431356986583473689/7373139198084828223356366156350000000000000)]
    bernstein := [(1335097414640287197455271546053682029829262456120757/24320556844515842344775712764101995056332800000000000000), (3030949356925122795934902179252868548183843818343861/30400696055644802930969640955127493820416000000000000000), (13803260561529097163656339389855267256493580143862047/114002610208668010991136153581728101826560000000000000000), (5654113447197733358894457391263708210445858437651893/47501087586945004579640063992386709094400000000000000000), (5555154341367380740678954094464106146899071589713333/59376359483681255724550079990483386368000000000000000000)]
    reserve := (343099/6250000000) }

theorem mixed_004_037_valid : mixed_004_037.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_037]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_037]
  · intro i; fin_cases i <;> norm_num [mixed_004_037]
  · norm_num [mixed_004_037]
  · norm_num [mixed_004_037, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_037, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_037, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_037, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_037]

def mixed_004_038 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/1280), (-3/5120)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(1809257/12500000), (2893297/20000000), (8477123/100000000), (14485501/100000000), (14485501/100000000), (16805659/100000000), (672227/4000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(22977/100000000), 0, 0, 0, 0]] i.1) i.2
    mu := ![(5604309/100000000), (241/4000000), (16947/400000), (16566/390625), (1/100000000), (2803097/50000000), (83/10000000)]
    alternative := .zero
    polynomial := [(-365549513413895615211868465422715613/237628955080350805842763200000000000000), (-16406334383/3320000000), (-445591436626488571051464783769506969115613/118814477540175402921381600000000000000), (-16406334383/3320000000), (-891182507703463728207314355670548515515613/237628955080350805842763200000000000000)]
    bernstein := [(21272369799062478553233899011414409336098525987/637880369157974852063696038920192000000000000000000), (28497668952424027640794444594990042779304279823/364503068090271344036397736525824000000000000000000), (3036477204959545739629513001214018364139422876849/30618257719582792899057409868169216000000000000000000), (561732033482229189541850481057885039272096380807/5832049089444341504582363784413184000000000000000000), (11368812394305560879754876199620248945936793865747/163297374504441562128306185963569152000000000000000000)]
    reserve := (1333941/40000000000) }

theorem mixed_004_038_valid : mixed_004_038.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_038]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_038]
  · intro i; fin_cases i <;> norm_num [mixed_004_038]
  · norm_num [mixed_004_038]
  · norm_num [mixed_004_038, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_038, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_038, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_038, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_038]

def mixed_004_039 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/5120), (-1/2560)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(7238339/50000000), (3617817/25000000), (4239229/50000000), (2896971/20000000), (2896971/20000000), (16801939/100000000), (16801947/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(2051/12500000), 0, 0, 0, 0]] i.1) i.2
    mu := ![(1401007/25000000), (4499/100000000), (4237963/100000000), (2120463/50000000), (1/100000000), (44843/800000), (83/10000000)]
    alternative := .zero
    polynomial := [(-16370243417502639247816379487261548513647/21082247598486403715743443507300000000000000), (-37463581407/10375000000), (-40761682268304859100859959836761768277838663647/10541123799243201857871721753650000000000000), (-37463581407/10375000000), (-81523348166366300699080671857144049294128813647/21082247598486403715743443507300000000000000)]
    bernstein := [(169418761826282464710077271288879604261302901525672193/14487610233867782889563355230444325961728000000000000000000), (410326429648290526355900048917284414623503498955695531/7243805116933891444781677615222162980864000000000000000000), (836779344869891831868292399155008114486797786412361131/10865707675400837167172516422833244471296000000000000000000), (131822213817966254173647035137831767289668154002423059/1810951279233472861195419403805540745216000000000000000000), (39829292315779941148824272008704718309854652048107953/905475639616736430597709701902770372608000000000000000000)]
    reserve := (2923511/250000000000) }

theorem mixed_004_039_valid : mixed_004_039.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_039]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_039]
  · intro i; fin_cases i <;> norm_num [mixed_004_039]
  · norm_num [mixed_004_039]
  · norm_num [mixed_004_039, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_039, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_039, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_039, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_039]

def mixed_004_040 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/2560), (-3/10240)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(2895729/20000000), (14474857/100000000), (8479459/100000000), (1448437/10000000), (1448437/10000000), (16799147/100000000), (16799151/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(2871/25000000), 0, 0, 0, 0]] i.1) i.2
    mu := ![(5603817/100000000), (1507/50000000), (2119437/50000000), (1060237/25000000), (1/100000000), (5604761/100000000), (83/20000000)]
    alternative := .zero
    polynomial := [(-219180016589247683011282785050757266735557/294262283094302801927330840753100000000000000), (-102467790697/20750000000), (-1102839001687817906490833670929321906199770885557/147131141547151400963665420376550000000000000), (-102467790697/20750000000), (-2205677784195619223733984330575858761642275035557/294262283094302801927330840753100000000000000)]
    bernstein := [(3727025392510582453190434120274593929481592744595139/92251597250826585270003775883704270848000000000000000000), (288646765674414439392570549814619052730249719093411539/4595806844859360793451097198569994584064000000000000000000), (44466260438412712084428747086531442279594829080735550361/606646503521435624735544830211239285096448000000000000000000), (58138109394768674430996285568200023124506338046682123161/808862004695247499647393106948319046795264000000000000000000), (189404471654434133529785201399906580662812904749707502283/3235448018780989998589572427793276187181056000000000000000000)]
    reserve := (40400659/1000000000000) }

theorem mixed_004_040_valid : mixed_004_040.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_040]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_040]
  · intro i; fin_cases i <;> norm_num [mixed_004_040]
  · norm_num [mixed_004_040]
  · norm_num [mixed_004_040, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_040, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_040, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_040, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_040]

def mixed_004_041 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/10240), (-1/5120)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(3619989/25000000), (57909/400000), (4240063/50000000), (7242023/50000000), (7242023/50000000), (8398643/50000000), (2099661/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(4101/50000000), 0, 0, 0, 0]] i.1) i.2
    mu := ![(5603677/100000000), (2251/100000000), (4239481/100000000), (2120481/50000000), (1/100000000), (5604351/100000000), (83/20000000)]
    alternative := .zero
    polynomial := [(-320317500825855667903288214197975609391981/879119345892161655820813414550850000000000000), (-37446868419/10375000000), (-3397815149986840161884101396666339724015620991981/439559672946080827910406707275425000000000000), (-37446868419/10375000000), (-6795629979656179497912534890044465250055632591981/879119345892161655820813414550850000000000000)]
    bernstein := [(285980771930398569121576302912438862459898079684025188739/9666019430112630411508740228131817674244096000000000000000000), (251542565596268280485378284010780350634808623228028944513/4833009715056315205754370114065908837122048000000000000000000), (451070423056083202636756588914102157510048208117009219713/7249514572584472808631555171098863255683072000000000000000000), (72625885355129380203366982068319289122192658952080272057/1208252428764078801438592528516477209280512000000000000000000), (27614043309974515032435074133416815275242817350941795219/604126214382039400719296264258238604640256000000000000000000)]
    reserve := (14793099/500000000000) }

theorem mixed_004_041_valid : mixed_004_041.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_041]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_041]
  · intro i; fin_cases i <;> norm_num [mixed_004_041]
  · norm_num [mixed_004_041]
  · norm_num [mixed_004_041, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_041, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_041, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_041, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_041]

def mixed_004_042 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/5120), (-1/10240)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(3620317/25000000), (3619911/25000000), (4240397/50000000), (7241861/50000000), (7241861/50000000), (671817/4000000), (8397713/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(4921/100000000), 0, 0, 0, 0]] i.1) i.2
    mu := ![(5603537/100000000), (93/6250000), (530011/12500000), (4240977/100000000), (1/100000000), (2801971/50000000), (83/20000000)]
    alternative := .zero
    polynomial := [(-41329049589708696228793468117331643463/363225606721173211944354672948000000000000), (-47334197933/20750000000), (-1490391833443295064202377452733382687649103463/181612803360586605972177336474000000000000), (-47334197933/20750000000), (-2980783625557540538696058676673297257966563463/363225606721173211944354672948000000000000)]
    bernstein := [(4669291149108159726407051668988992027592769383862137/249606736309951477768364782741829745377280000000000000000), (6868615603390974652636386153664458026679128957824979/166404490873300985178909855161219830251520000000000000000), (11705302898099165165304372893646514204424970125365847/230406218132262902555413645607842841886720000000000000000), (31474014913857438547568027155927491239813907189837779/665617963493203940715639420644879321006080000000000000000), (122703293089284733423017576154927733941751691360898937/3993707780959223644293836523869275926036480000000000000000)]
    reserve := (18706591/1000000000000) }

theorem mixed_004_042_valid : mixed_004_042.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_042]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_042]
  · intro i; fin_cases i <;> norm_num [mixed_004_042]
  · norm_num [mixed_004_042]
  · norm_num [mixed_004_042, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_042, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_042, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_042, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_042]

def mixed_004_043 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/10240), 0⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14482579/100000000), (7241019/50000000), (8481461/100000000), (7241699/50000000), (7241699/50000000), (16793563/100000000), (16793563/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(41/2500000), 0, 0, 0, 0]] i.1) i.2
    mu := ![(5603397/100000000), (91/12500000), (848139/20000000), (4240991/100000000), (1/100000000), (1400883/25000000), (83/20000000)]
    alternative := .zero
    polynomial := [(5284401843905608604165353455778076907/789847710372824185592385976100000000000000), (-1978076743/2075000000), (-46043170729111357836785813217509854781573471/4758118737185687865014373350000000000000), (-1978076743/2075000000), (-7643166346316887244812053598271989349519273093/789847710372824185592385976100000000000000)]
    bernstein := [(65136650568600355121005030933887476636856048735933307/8684467417271705201349458314133856321536000000000000000000), (11498115004058873378359927443978419194453712007/378612732686580339763072785040015360000000000000000), (9406118142814188366775247695934661917019731507/248464605825568347969516515182510080000000000000000), (757346109908700627723432265857023401649/25275126731930373938956351235200000000000000), (5284401843905608604165353455778076907/789847710372824185592385976100000000000000)]
    reserve := (1338081/200000000000) }

theorem mixed_004_043_valid : mixed_004_043.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_043]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_043]
  · intro i; fin_cases i <;> norm_num [mixed_004_043]
  · norm_num [mixed_004_043]
  · norm_num [mixed_004_043, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_043, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_043, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_043, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_043]

def mixed_004_044 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨0, (1/10240)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(905257/6250000), (905257/6250000), (4240997/50000000), (14483043/100000000), (14483043/100000000), (8396031/50000000), (16791633/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(707/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5603281/100000000), (179/50000000), (848243/20000000), (2120491/50000000), (1/100000000), (2801593/50000000), (209/25000000)]
    alternative := .zero
    polynomial := [(52753030305970418556883306046823831053/14404628263782317506968828859350000000000000), (8125835899/8950000000), (-6045257554609201962916193260309267260473072177/654755830171923523044037675425000000000000), (8125835899/8950000000), (-132995666254155473490126670283687185777231418947/14404628263782317506968828859350000000000000)]
    bernstein := [(52753030305970418556883306046823831053/14404628263782317506968828859350000000000000), (47621677494245357820931723865087532709159/1843792417764136640892010093996800000000000000), (150977567667179589886754742421869997265785364453/4531304245897142208656204007006535680000000000000000), (5052683459484780465244751900455948553721827467559/193335647824944734235998037632278855680000000000000000), (61545483587732955109956330225862552550036174270542423/14398232972563156935102690220760258052096000000000000000000)]
    reserve := (3662227/1000000000000) }

theorem mixed_004_044_valid : mixed_004_044.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_044]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_044]
  · intro i; fin_cases i <;> norm_num [mixed_004_044]
  · norm_num [mixed_004_044]
  · norm_num [mixed_004_044, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_044, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_044, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_044, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_044]

def mixed_004_045 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/10240), (1/5120)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(7242933/50000000), (14485867/100000000), (8482391/100000000), (14482659/100000000), (14482659/100000000), (16790921/100000000), (4197409/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1061/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1400797/25000000), (179/50000000), (4241649/100000000), (4240949/100000000), (1/100000000), (1120581/20000000), (1689/100000000)]
    alternative := .zero
    polynomial := [(-10293547052393725763972542098805036199623/94854165125347718018353787046300000000000000), (18374849731/8950000000), (-357153272225696273928446612765275000471595699623/47427082562673859009176893523150000000000000), (18374849731/8950000000), (-714306534157845495463167461558007902138155199623/94854165125347718018353787046300000000000000)]
    bernstein := [(21022230851345455167902875729492768992784268904342950777/1042932574983045605163672174391313760780288000000000000000000), (5974559705762401328480092581362800717924242625486511059/173822095830507600860612029065218960130048000000000000000000), (4091686526570624723313400583903353786445674451009687933/111742775891040600553250590113355045797888000000000000000000), (1168640778159578598048347648940574131338516397814242259/43455523957626900215153007266304740032512000000000000000000), (338891911750637716554049522484643202933091056425177977/65183285936440350322729510899457110048768000000000000000000)]
    reserve := (5199061/1000000000000) }

theorem mixed_004_045_valid : mixed_004_045.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_045]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_045]
  · intro i; fin_cases i <;> norm_num [mixed_004_045]
  · norm_num [mixed_004_045]
  · norm_num [mixed_004_045, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_045, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_045, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_045, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_045]

def mixed_004_046 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/5120), (3/10240)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(724381/5000000), (7243811/50000000), (8482789/100000000), (579291/4000000), (579291/4000000), (839489/5000000), (16787639/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(3537/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(700387/12500000), (179/50000000), (2121041/50000000), (1060229/25000000), (1/100000000), (5602623/100000000), (159/6250000)]
    alternative := .zero
    polynomial := [(-42863743639053827417519890920987757591/128793445873717675442807024220000000000000), (3578293361/1118750000), (-149632773929219687185243117448777166586044197/21465574312286279240467837370000000000000), (3578293361/1118750000), (-897796600711574484057631287172772078528507591/128793445873717675442807024220000000000000)]
    bernstein := [(766351402305084712534476164869670757323262690237203/29502060691560723304746585998078928486400000000000000000), (6653007348004173402006539028821715519738627131405227/177012364149364339828479515988473570918400000000000000000), (46368657499112983059508666219978871576552265719691/1216579822332400961020477773116656844800000000000000000), (19516021102213089133090557257885109521896270710903043/708049456597457359313918063953894283673600000000000000000), (8400831771592521328095842133667850191876522445976329/1416098913194914718627836127907788567347200000000000000000)]
    reserve := (741547/125000000000) }

theorem mixed_004_046_valid : mixed_004_046.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_046]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_046]
  · intro i; fin_cases i <;> norm_num [mixed_004_046]
  · norm_num [mixed_004_046]
  · norm_num [mixed_004_046, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_046, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_046, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_046, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_046]

def mixed_004_047 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/10240), (1/2560)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(7244687/50000000), (14489377/100000000), (4241593/50000000), (14481891/100000000), (14481891/100000000), (16788639/100000000), (8392821/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1981/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5603003/100000000), (179/50000000), (848503/20000000), (4240883/100000000), (1/100000000), (5602341/100000000), (17/500000)]
    alternative := .zero
    polynomial := [(-23000543652293301769837254151892218944529/34371779751768162885116501036100000000000000), (155535798857/35800000000), (-115027745464218904472887317292349866006434579529/17185889875884081442558250518050000000000000), (155535798857/35800000000), (-230055467927894156652472864747445580120650214529/34371779751768162885116501036100000000000000)]
    bernstein := [(11026910021339428726425782853138096280641501128516315951/377921715044247699879875525375999015387136000000000000000000), (3731998105132213671819626558506243013240065479245078117/94480428761061924969968881343999753846784000000000000000000), (2776605737876940840206710624285325218701029629992316517/70860321570796443727476661007999815385088000000000000000000), (166697254029755194084709284029589863133415336377215613/5905026797566370310623055083999984615424000000000000000000), (9797550196389628491659852206771582607325563951436671/1476256699391592577655763770999996153856000000000000000000)]
    reserve := (414797/62500000000) }

theorem mixed_004_047_valid : mixed_004_047.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_047]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_047]
  · intro i; fin_cases i <;> norm_num [mixed_004_047]
  · norm_num [mixed_004_047]
  · norm_num [mixed_004_047, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_047, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_047, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_047, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_047]

def mixed_004_048 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/2560), (1/2048)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14491127/100000000), (14491133/100000000), (33139/390625), (7240753/50000000), (7240753/50000000), (16787497/100000000), (8391823/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(199/1562500), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5602911/100000000), (179/50000000), (4242949/100000000), (84817/2000000), (1/100000000), (5602059/100000000), (851/20000000)]
    alternative := .zero
    polynomial := [(-1732231083393382337058198037068848644111/1550142893044488848474662926300000000000000), (24572020053/4475000000), (-5059588224758358300146350778029593397350994111/775071446522244424237331463150000000000000), (24572020053/4475000000), (-10119174717285633206910364497861149725853344111/1550142893044488848474662926300000000000000)]
    bernstein := [(2087915362396249697038305550101699006407904036396689/66578130297529054772353767530821582848000000000000000000), (726271635446356549800041092999438966603966544426203/17754168079341081272627671341552422092800000000000000000), (222746671832243809189507246797396191969867066853061/5557826529185034137518227550399019089920000000000000000), (65615117981065617622618831897504988118570711045983/2272533514155658402896341931718710027878400000000000000), (7954656956164924870166399055008377572430443053369/1090816086794716033390244127224980813381632000000000000)]
    reserve := (729239/100000000000) }

theorem mixed_004_048_valid : mixed_004_048.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_048]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_048]
  · intro i; fin_cases i <;> norm_num [mixed_004_048]
  · norm_num [mixed_004_048]
  · norm_num [mixed_004_048, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_048, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_048, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_048, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_048]

def mixed_004_049 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/2048), (3/5120)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14492881/100000000), (14492889/100000000), (8483981/100000000), (14481121/100000000), (7240561/50000000), (3357271/20000000), (16781651/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(15569/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5602819/100000000), (179/50000000), (4243383/100000000), (4240817/100000000), (1/100000000), (5601777/100000000), (5111/100000000)]
    alternative := .zero
    polynomial := [(-5780863940963155122471181159801455665361749/3444782657271943054995274467774780000000000000), (237655450957/35800000000), (-11054851460095653079217323510569276168186178311749/1722391328635971527497637233887390000000000000), (237655450957/35800000000), (-22109697139327365195279524549957392534916691261749/3444782657271943054995274467774780000000000000)]
    bernstein := [(80042960453898059314646956394599366351234633323645571/2424050295572229652411028811552601865190585139200000000000), (1274645003152417049870949040181121768086223366562315693/30300628694652870655137860144407523314882314240000000000000), (6640912368475939153242207161527309003519835366048207119/162324796578497521366809965059326017758298112000000000000000), (27984777529928217481436496875125682639014783462885971817/946894646707902207973058129512735103590072320000000000000000), (18927551592651932232923174115146613034392437112949417531/2367236616769755519932645323781837758975180800000000000000000)]
    reserve := (7995631/1000000000000) }

theorem mixed_004_049_valid : mixed_004_049.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_049]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_049]
  · intro i; fin_cases i <;> norm_num [mixed_004_049]
  · norm_num [mixed_004_049]
  · norm_num [mixed_004_049, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_049, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_049, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_049, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_049]

def mixed_004_050 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/5120), (7/10240)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(7247317/50000000), (7247323/50000000), (8484379/100000000), (452523/3125000), (14480737/100000000), (16785213/100000000), (3355931/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(18401/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5602727/100000000), (179/50000000), (4243817/100000000), (265049/6250000), (1/100000000), (1120299/20000000), (2983/50000000)]
    alternative := .zero
    polynomial := [(-443083211763862751585499405556404223929947/188491823818058605045508960185650000000000000), (139365107013/17900000000), (-597581342775752081185821058996645962878658054947/94245911909029302522754480092825000000000000), (139365107013/17900000000), (-62903275919383810447836343815467703650162746313/9920622306213610791868892641350000000000000)]
    bernstein := [(342763578143725537607890487351845834800245640990464761/9963891924454837697007280931351788781568000000000000000000), (858387746879467906033137028001355675969481052887331909/19927783848909675394014561862703577563136000000000000000000), (64772135513735753390870083593135786946602372757539779719/1554367140214954680733135825290879049924608000000000000000000), (82979291602657754341573781038677651786029830884423281/2748659841228920744002008532786700353536000000000000000000), (47434845136687677947684983124814316405341228671415389/5497319682457841488004017065573400707072000000000000000000)]
    reserve := (4314361/500000000000) }

theorem mixed_004_050_valid : mixed_004_050.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_050]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_050]
  · intro i; fin_cases i <;> norm_num [mixed_004_050]
  · norm_num [mixed_004_050]
  · norm_num [mixed_004_050, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_050, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_050, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_050, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_050]

def mixed_004_051 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(7/10240), (1/1280)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(3624097/25000000), (14496403/100000000), (8484777/100000000), (14480351/100000000), (14480351/100000000), (1678407/10000000), (838883/5000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(4247/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1120527/20000000), (179/50000000), (4244251/100000000), (4240751/100000000), (1/100000000), (5601213/100000000), (6821/100000000)]
    alternative := .zero
    polynomial := [(-480567633050898623123219040304377833255807/153252235271344412831369619338010000000000000), (63968784453/7160000000), (-481428926229540275945170107487866671455476155807/76626117635672206415684809669005000000000000), (63968784453/7160000000), (-962857371891447500991717091756693038533119055807/153252235271344412831369619338010000000000000)]
    bernstein := [(59973010199021125631897014766049747314439156314242533793/1685026146635064164001421511538488626485657600000000000000000), (3089184180220635978218218872565901297265919769455408733/70209422776461006833392562980770359436902400000000000000000), (3350656488349344972864796146632278904867478725552530771/78985600623518632687566633353366654366515200000000000000000), (33850104975653308131202456829675131846192378618139117/1097022230882203231771758796574536866201600000000000000000), (3828047998291094974858028320593748951749218842646593/411383336580826211914409548715451324825600000000000000000)]
    reserve := (4652653/500000000000) }

theorem mixed_004_051_valid : mixed_004_051.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_051]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_051]
  · intro i; fin_cases i <;> norm_num [mixed_004_051]
  · norm_num [mixed_004_051]
  · norm_num [mixed_004_051, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_051, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_051, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_051, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_051]

def mixed_004_052 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/1280), (9/10240)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14498141/100000000), (14498161/100000000), (4242587/50000000), (7239983/50000000), (7239983/50000000), (16782927/100000000), (3355133/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(24069/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5602543/100000000), (179/50000000), (848937/20000000), (4240717/100000000), (1/100000000), (5600931/100000000), (1919/25000000)]
    alternative := .zero
    polynomial := [(-133764837056701638871634077157932391246967/33166704266398331113249582372100000000000000), (360967613249/35800000000), (-103450286706044922682830268030995466503534121967/16583352133199165556624791186050000000000000), (360967613249/35800000000), (-206900439647252788664021664427913775074676996967/33166704266398331113249582372100000000000000)]
    bernstein := [(3264032428220427149000735670467324008197834482017433/89031193837677814900241392858642251776000000000000000000), (31949914094577672404860502736605863534159912228409697/712249550701422519201931142869138014208000000000000000000), (5544426480904777865983090964625067561864765277553343/128526234713038650081551484427513626624000000000000000000), (1436070772885428290113797480002810718502762911738023857/45583971244891041228923593143624832909312000000000000000000), (3629895354214530728739886412625777771370044221311309113/364671769959128329831388745148998663274496000000000000000000)]
    reserve := (9953869/1000000000000) }

theorem mixed_004_052_valid : mixed_004_052.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_052]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_052]
  · intro i; fin_cases i <;> norm_num [mixed_004_052]
  · norm_num [mixed_004_052]
  · norm_num [mixed_004_052, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_052, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_052, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_052, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_052]

def mixed_004_053 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(9/10240), (1/1024)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(7249947/50000000), (14499919/100000000), (2121393/25000000), (723979/5000000), (723979/5000000), (16781783/100000000), (16773671/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(3363/12500000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1400613/25000000), (179/50000000), (4245119/100000000), (1060171/25000000), (1/100000000), (700081/12500000), (8531/100000000)]
    alternative := .zero
    polynomial := [(-199904288943015596214391383969113663087197/39640240895340321306186653940900000000000000), (100528942303/8950000000), (-122940305765143915836464399178104182710728087197/19820120447670160653093326970450000000000000), (100528942303/8950000000), (-245880411625998888657332583964824396307793087197/39640240895340321306186653940900000000000000)]
    bernstein := [(16408525684961411947991625972189937483417971767636334083/435849057922684003328521423738457643024384000000000000000000), (284408588827338082345905401686182950450710734227749181/6226415113181200047550306053406537757491200000000000000000), (573348066492802053375684824264854042112043853891973177/13075471737680520099855642712153729290731520000000000000000), (117794349642168542758391751586282639988700200953181/3662597125400705910323709443180316327936000000000000000), (27213976893674442121885333792402546412759778727411/2563817987780494137226596610226221429555200000000000000)]
    reserve := (10614629/1000000000000) }

theorem mixed_004_053_valid : mixed_004_053.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_053]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_053]
  · intro i; fin_cases i <;> norm_num [mixed_004_053]
  · norm_num [mixed_004_053]
  · norm_num [mixed_004_053, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_053, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_053, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_053, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_053]

def mixed_004_054 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/1024), (11/10240)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(906353/6250000), (7250839/50000000), (848597/10000000), (2895839/20000000), (2895839/20000000), (16780639/100000000), (16771677/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1487/5000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5602361/100000000), (179/50000000), (4245553/100000000), (4240651/100000000), (1/100000000), (2800183/50000000), (1877/20000000)]
    alternative := .zero
    polynomial := [(-175520376527728510619690688430995055682472679/28468387062120972577744679413136100000000000000), (110822106113/8950000000), (-87884000045487162309000757688584880927092134372679/14234193531060486288872339706568050000000000000), (110822106113/8950000000), (-175767824570597796889490895686481330859128586272679/28468387062120972577744679413136100000000000000)]
    bernstein := [(1207568725726402133414602498930375454633384576375685209/31301322598829848989984311172460549708028313600000000000000), (4849258401965388195040210135121413858917119943606774769/104337741996099496633281037241535165693427712000000000000000), (418442855549536410506588502659791494062216386895012822579/9390396779648954696995293351738164912408494080000000000000000), (342554877975522854888969664530696427215944840607944623337/10433774199609949663328103724153516569342771200000000000000000), (3533427637708272921097358954387588527660366194346649149961/313013225988298489899843111724605497080283136000000000000000000)]
    reserve := (11288429/1000000000000) }

theorem mixed_004_054_valid : mixed_004_054.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_054]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_054]
  · intro i; fin_cases i <;> norm_num [mixed_004_054]
  · norm_num [mixed_004_054]
  · norm_num [mixed_004_054, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_054, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_054, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_054, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_054]

def mixed_004_055 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(11/10240), (3/2560)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14503401/100000000), (14503437/100000000), (8486367/100000000), (1809851/12500000), (1809851/12500000), (3355899/20000000), (16769683/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(509/1562500), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5602269/100000000), (179/50000000), (1061497/25000000), (4240617/100000000), (1/100000000), (5600083/100000000), (10239/100000000)]
    alternative := .zero
    polynomial := [(-1418832772213211199313607576807928997766331/191726899266496956847293220559380000000000000), (24223552837/1790000000), (-589608950536513119388138325360039511809081616331/95863449633248478423646610279690000000000000), (24223552837/1790000000), (-1179216482240254025565077337112502215689165466331/191726899266496956847293220559380000000000000)]
    bernstein := [(83197349775764810114597422539455430625414003753818212629/2108059551009512494445177979968132930653388800000000000000000), (24900488311525386734616894170833979004858393650504601117/527014887752378123611294494992033232663347200000000000000000), (17887168811436940737385141685860930091989795495027627823/395261165814283592708470871244024924497510400000000000000000), (1102909135800106822393951413874766669289144287925389293/32938430484523632725705905937002077041459200000000000000000), (98303901672930227873226119660942971617834222004318389/8234607621130908181426476484250519260364800000000000000000)]
    reserve := (11937897/1000000000000) }

theorem mixed_004_055_valid : mixed_004_055.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_055]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_055]
  · intro i; fin_cases i <;> norm_num [mixed_004_055]
  · norm_num [mixed_004_055]
  · norm_num [mixed_004_055, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_055, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_055, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_055, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_055]

def mixed_004_056 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/2560), (13/10240)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(7252577/50000000), (14505197/100000000), (1697353/20000000), (7239211/50000000), (7239211/50000000), (335567/2000000), (1676769/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(35413/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2801089/50000000), (179/50000000), (2123211/50000000), (530073/12500000), (1/100000000), (27999/500000), (5547/50000000)]
    alternative := .zero
    polynomial := [(-110061074250106817009573236254063067/12581313791414307420748531500000000000), (525678207401/35800000000), (-38566174272400072368963638547742484920567/6290656895707153710374265750000000000), (525678207401/35800000000), (-77132238483725894631110267522248715778067/12581313791414307420748531500000000000)]
    bernstein := [(21779846687424264433153895835352677492033214973/540363312748382159586050546325258240000000000000000), (103737949415390154815213494653886329612153578483/2161453250993528638344202185301032960000000000000000), (1191530910905567136840091941864741070430611265879/25937439011922343660130426223612395520000000000000000), (1180612146516123493715549364861528471374566920403/34583252015896458213507234964816527360000000000000000), (1742079416506856974647210364547088708715607498813/138333008063585832854028939859266109440000000000000000)]
    reserve := (6296687/500000000000) }

theorem mixed_004_056_valid : mixed_004_056.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_056]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_056]
  · intro i; fin_cases i <;> norm_num [mixed_004_056]
  · norm_num [mixed_004_056]
  · norm_num [mixed_004_056, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_056, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_056, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_056, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_056]

def mixed_004_057 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(13/10240), (7/5120)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14506907/100000000), (14506957/100000000), (8487163/100000000), (3619509/25000000), (3619509/25000000), (3355441/20000000), (16765697/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(38251/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5602087/100000000), (359/100000000), (4246857/100000000), (4240551/100000000), (1/100000000), (5599517/100000000), (2987/25000000)]
    alternative := .zero
    polynomial := [(-5873343401927871939833002174132106717566229/576940088894858260327474286101380000000000000), (566943382653/35900000000), (-1758971701987854395209907199278414250956423341229/288470044447429130163737143050690000000000000), (566943382653/35900000000), (-3517937530632306862547874565554654369806129116229/576940088894858260327474286101380000000000000)]
    bernstein := [(260872203840821864512320926696753500709162905616583588331/6343523362700157467294608151261118567599308800000000000000000), (2238459404899711780374479262791781861049736405619169261/45967560599276503386192812690297960634777600000000000000000), (221596565081952638177589740677668814274231549501983366153/4757642522025118100470956113445838925699481600000000000000000), (399522188644304722548894067871683740804613015791084181/11491890149819125846548203172574490158694400000000000000000), (5258116001055326849332808765985169158648147708119729371/396470210168759841705913009453819910474956800000000000000000)]
    reserve := (13262323/1000000000000) }

theorem mixed_004_057_valid : mixed_004_057.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_057]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_057]
  · intro i; fin_cases i <;> norm_num [mixed_004_057]
  · norm_num [mixed_004_057]
  · norm_num [mixed_004_057, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_057, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_057, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_057, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_057]

def mixed_004_058 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(7/5120), (3/2048)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14508659/100000000), (7254359/50000000), (8487561/100000000), (14477649/100000000), (14477649/100000000), (16776059/100000000), (3352741/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(41089/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1400499/25000000), (359/100000000), (1061823/25000000), (4240517/100000000), (1/100000000), (2799617/50000000), (12801/100000000)]
    alternative := .zero
    polynomial := [(-10591171983678021081136770870137058658324777/901463607379694819200053812190300000000000000), (152046263523/8975000000), (-2741929139137969032078177222584615421427877824777/450731803689847409600026906095150000000000000), (152046263523/8975000000), (-5483847687103954386135273308398360705797097324777/901463607379694819200053812190300000000000000)]
    bernstein := [(25968841863093716961625953616856774213251526168933988023/619481073956795760467978240767594340548608000000000000000000), (12245638748149158076866090041626614422111362411777251187/247792429582718304187191296307037736219443200000000000000000), (14049368407671042003864157578036177450033685988837051357/297350915499261965024629555568445283463331840000000000000000), (1403846492482315865458260916513317163129572194087425019/39646788733234928669950607409126037795110912000000000000000), (220437656573800957590454661698173255760428572326934087/15858715493293971467980242963650415118044364800000000000000)]
    reserve := (2780019/200000000000) }

theorem mixed_004_058_valid : mixed_004_058.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_058]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_058]
  · intro i; fin_cases i <;> norm_num [mixed_004_058]
  · norm_num [mixed_004_058]
  · norm_num [mixed_004_058, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_058, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_058, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_058, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_058]

def mixed_004_059 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/2048), (1/640)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(3627603/25000000), (14510479/100000000), (4243979/50000000), (14477261/100000000), (14477263/100000000), (16774913/100000000), (16761713/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(5491/12500000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1120381/20000000), (359/100000000), (2123863/50000000), (1060121/25000000), (1/100000000), (5598951/100000000), (2731/20000000)]
    alternative := .zero
    polynomial := [(-18597671676797378894398887587174370953926501/1384747173422847999628411047857700000000000000), (324725615723/17950000000), (-4203350367267335401215232403383109303679408226501/692373586711423999814205523928850000000000000), (324725615723/17950000000), (-8406682136862994005051570407878631432987862526501/1384747173422847999628411047857700000000000000)]
    bernstein := [(1040340130630147554567224528237248395067627269856979531/24360729899333929113940154789863065033847603200000000000000), (381733588756555678016147697717360630529816636524658201/7612728093541852848106298371832207823077376000000000000000), (48870807720609843487122110825096927132955821516314847/1019561798242212435014236389084670690590720000000000000000), (26817537745009294291803022416999298421509668785688977/743430477884946567197880700374239045222400000000000000000), (3383246464636848107910685928511539383237687295694299/232322024339045802249337718866949701632000000000000000000)]
    reserve := (2912549/200000000000) }

theorem mixed_004_059_valid : mixed_004_059.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_059]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_059]
  · intro i; fin_cases i <;> norm_num [mixed_004_059]
  · norm_num [mixed_004_059]
  · norm_num [mixed_004_059, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_059, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_059, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_059, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_059]

def mixed_004_060 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/640), (17/10240)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(2902433/20000000), (181403/1250000), (2122089/25000000), (23163/160000), (23163/160000), (16773767/100000000), (16759721/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(2923/6250000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1120363/20000000), (359/100000000), (4248161/100000000), (84809/2000000), (1/100000000), (1399667/25000000), (3627/25000000)]
    alternative := .zero
    polynomial := [(-373334036354024021256524573978921913479033/24521506085557142862282726699900000000000000), (345370959999/17950000000), (-222908185358734345030595113488176410042162562099/36782259128335714293424090049850000000000000), (345370959999/17950000000), (-445815250715359627989126457402630883318584687099/73564518256671428586848180099700000000000000)]
    bernstein := [(41272983819865774625824004178902389916873303074777/949390625175476921869328212876591104000000000000000000), (10043733308537144368163816348072417324358959339116117/197473250036499199748820268278330949632000000000000000000), (460825755810403668096710541279736012609779282106761967/9478716001751961587943372877359885582336000000000000000000), (1857328535104405106117244083123075864952791062248052213/50553152009343795135697988679252723105792000000000000000000), (12319503873969167062210138050052933607739227764695377221/808850432149500722171167818868043569692672000000000000000000)]
    reserve := (95193/6250000000) }

theorem mixed_004_060_valid : mixed_004_060.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_060]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_060]
  · intro i; fin_cases i <;> norm_num [mixed_004_060]
  · norm_num [mixed_004_060]
  · norm_num [mixed_004_060, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_060, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_060, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_060, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_060]

def mixed_004_061 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(17/10240), (9/5120)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(7256959/50000000), (7257001/50000000), (4244377/50000000), (1809561/12500000), (1809561/12500000), (838631/5000000), (1675773/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(6201/12500000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1400431/25000000), (359/100000000), (1062149/25000000), (4240417/100000000), (1/100000000), (1119677/20000000), (15361/100000000)]
    alternative := .zero
    polynomial := [(-3336012190906974768006097490369203904892859/194729803906485232931270136199645000000000000), (183010665339/8975000000), (-589139402116327321799602723824637707952192792859/97364901953242616465635068099822500000000000), (183010665339/8975000000), (-1178275468220463736624437441551785046700480692859/194729803906485232931270136199645000000000000)]
    bernstein := [(94709935627516001080147552137549180488541990253246168261/2141076836697208621431673473840488964633395200000000000000000), (55209940447224512289652565179010031532669847379188109597/1070538418348604310715836736920244482316697600000000000000000), (79153437498639573355894004183300707540090718243620555807/1605807627522906466073755105380366723475046400000000000000000), (10008004134150870985216784798341603292838275110329494413/267634604587151077678959184230061120579174400000000000000000), (2124888692232244606024644546913704704445674978834836901/133817302293575538839479592115030560289587200000000000000000)]
    reserve := (3969757/250000000000) }

theorem mixed_004_061_valid : mixed_004_061.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_061]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_061]
  · intro i; fin_cases i <;> norm_num [mixed_004_061]
  · norm_num [mixed_004_061]
  · norm_num [mixed_004_061, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_061, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_061, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_061, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_061]

def mixed_004_062 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(9/5120), (19/10240)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(1451567/10000000), (2903153/20000000), (132643/1562500), (14476101/100000000), (14476101/100000000), (16771473/100000000), (16755739/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(52449/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2800817/50000000), (359/100000000), (531129/12500000), (4240383/100000000), (1/100000000), (2799051/50000000), (8107/50000000)]
    alternative := .zero
    polynomial := [(-3644935624897625648850110328067709048213553/190323099758862968689101254121100000000000000), (773367979087/35900000000), (-575023763158539500612323179421517827495105963553/95161549879431484344550627060550000000000000), (773367979087/35900000000), (-1150043881381454103598997508732707587281163713553/190323099758862968689101254121100000000000000)]
    bernstein := [(5881925066005032285199718983815294389963362089755660367/130789038262025909866425900493233555767296000000000000000000), (1953162352405146976925345323634699271338558139772895971/37368296646293117104693114426638158790656000000000000000000), (78408637803963232915714825500437057293461572007869180581/1569468459144310918397110805918802669207552000000000000000000), (5686719061647427860417990273459132633428702400546708651/149473186585172468418772457706552635162624000000000000000000), (34584729753178621744316596464345386932030400959536657887/2092624612192414557862814407891736892276736000000000000000000)]
    reserve := (16526963/1000000000000) }

theorem mixed_004_062_valid : mixed_004_062.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_062]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_062]
  · intro i; fin_cases i <;> norm_num [mixed_004_062]
  · norm_num [mixed_004_062]
  · norm_num [mixed_004_062, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_062, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_062, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_062, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_062]

def mixed_004_063 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(19/10240), (1/512)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14517423/100000000), (1814691/12500000), (169791/2000000), (14475713/100000000), (14475713/100000000), (8385163/50000000), (4188437/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(55291/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(700193/12500000), (359/100000000), (4249467/100000000), (84807/2000000), (1/100000000), (2798909/50000000), (17067/100000000)]
    alternative := .zero
    polynomial := [(-42641231832815946037654619716200827892199/2003413476266151745273181804587500000000000), (25459932241/1121875000), (-6045639670824657684555879872526151574747892199/1001706738133075872636590902293750000000000), (25459932241/1121875000), (-12091236700417482553165722090432586948667892199/2003413476266151745273181804587500000000000)]
    bernstein := [(77452627553477365543734460610416453108131284341064717/1694443394152131729274414953662144053248000000000000000000), (4166932979667952613472896465469232794831882547139/78664967230832485110232820504277811200000000000000000), (8365909676878391917684389055507720393076570335761347/165208230929832843604255457982059045191680000000000000000), (546650126093114185065247918004505331326989838089/14120361617934431077286791280517867110400000000000000), (7284291671122247912929367228530370019541570757/423610848538032932318603738415536013312000000000000)]
    reserve := (3439143/200000000000) }

theorem mixed_004_063_valid : mixed_004_063.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_063]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_063]
  · intro i; fin_cases i <;> norm_num [mixed_004_063]
  · norm_num [mixed_004_063]
  · norm_num [mixed_004_063, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_063, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_063, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_063, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_063]

def mixed_004_064 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/512), (21/10240)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(580767/4000000), (3629823/25000000), (2122487/25000000), (579013/4000000), (579013/4000000), (8384589/50000000), (8375879/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(29067/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2800727/50000000), (359/100000000), (4249903/100000000), (1060079/25000000), (1/100000000), (2798767/50000000), (14/78125)]
    alternative := .zero
    polynomial := [(-59663957932073642435971869885849926061257/2535591084412324234840261929400000000000000), (214023070843/8975000000), (-15286824434161336067851990541273785980348531889/2535591084412324234840261929400000000000000), (214023070843/8975000000), (-272977942325060785610884903025069645186115547/45278412221648647050718963025000000000000)]
    bernstein := [(40447386946498157139717069797729009022069958011/871222462686408637438971901667748872192000000000000), (52527414972281138444146725555060569291425244331/978901643467874873526934720974998732800000000000000), (4455425553873945698679359622039548178709288518437/86832803590007505392588561628014837760000000000000000), (77095490842920673613012355818164855968292015051999/1957803286935749747053869441949997465600000000000000000), (62254260937194258493013769875162722507170602857234451/3484889850745634549755887606670995488768000000000000000000)]
    reserve := (8932027/500000000000) }

theorem mixed_004_064_valid : mixed_004_064.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_064]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_064]
  · intro i; fin_cases i <;> norm_num [mixed_004_064]
  · norm_num [mixed_004_064]
  · norm_num [mixed_004_064, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_064, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_064, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_064, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_064]

def mixed_004_065 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(21/10240), (11/5120)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14520927/100000000), (453783/3125000), (1698069/20000000), (14474937/100000000), (14474937/100000000), (1676803/10000000), (2093721/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(60977/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1400341/25000000), (359/100000000), (2125169/50000000), (2120141/50000000), (1/100000000), (5597251/100000000), (4693/25000000)]
    alternative := .zero
    polynomial := [(-2432215653346068171326306738953920564422993/93946252431270692357234631568410000000000000), (56092297821/2243750000), (-21763674517812239524034321492258316769686909461/3613317401202718936816716598785000000000000), (56092297821/2243750000), (-565853105247464881556721032491977282091295222993/93946252431270692357234631568410000000000000)]
    bernstein := [(48702626061704620515490612086563623313703555650854640767/1032949969341614365177855722457421150001561600000000000000000), (28070991669752120489698749396585488792109132600069884897/516474984670807182588927861228710575000780800000000000000000), (40269225997168498202948328808473299199866202640801969981/774712477006210773883391791843065862501171200000000000000000), (5169196770169397507980021938742607297191121194303441057/129118746167701795647231965307177643750195200000000000000000), (91950939416019099934656601448924492511435000719728699/4966105621834684447970460204122217067315200000000000000000)]
    reserve := (18515703/1000000000000) }

theorem mixed_004_065_valid : mixed_004_065.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_065]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_065]
  · intro i; fin_cases i <;> norm_num [mixed_004_065]
  · norm_num [mixed_004_065]
  · norm_num [mixed_004_065, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_065, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_065, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_065, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_065]

def mixed_004_066 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(11/5120), (23/10240)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(363067/2500000), (726141/5000000), (8490743/100000000), (14474549/100000000), (14474549/100000000), (16766881/100000000), (8373889/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(63821/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2800637/50000000), (359/100000000), (4250773/100000000), (530031/12500000), (1/100000000), (5596967/100000000), (2453/12500000)]
    alternative := .zero
    polynomial := [(-88207096998571020261449883180735818870893349/3110074192891395253612896702717900000000000000), (58680362489/2243750000), (-9358351192544064981386044393676893796140306768349/1555037096445697626806448351358950000000000000), (58680362489/2243750000), (-18716614177991131391751827337470606856461742643349/3110074192891395253612896702717900000000000000)]
    bernstein := [(102318457035010752053920549293578352943864095589007892091/2137226711456342127052322749119938370207744000000000000000000), (78437748366491276069473615390928941826273545030809735021/1424817807637561418034881832746625580138496000000000000000000), (192944853215017694370897545102559145367619854671626884911/3663817219639443646375410427062751491784704000000000000000000), (232005519441824253611715666173406804570041198308946662629/5699271230550245672139527330986502320553984000000000000000000), (656149198469167493726520359498548599844104834875479993291/34195627383301474032837163985919013923323904000000000000000000)]
    reserve := (9594051/500000000000) }

theorem mixed_004_066_valid : mixed_004_066.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_066]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_066]
  · intro i; fin_cases i <;> norm_num [mixed_004_066]
  · norm_num [mixed_004_066]
  · norm_num [mixed_004_066, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_066, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_066, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_066, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_066]

def mixed_004_067 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(23/10240), (3/1280)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(907777/6250000), (2904917/20000000), (8491141/100000000), (180927/1250000), (180927/1250000), (16765733/100000000), (16745789/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(13333/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(175037/3125000), (359/100000000), (4251209/100000000), (2120107/50000000), (1/100000000), (5596683/100000000), (5119/25000000)]
    alternative := .zero
    polynomial := [(-33476002104429748891136354493298726613977001/1081730625945759155042639822862200000000000000), (980304935527/35900000000), (-3252513533544019767305182427065829249094632227001/540865312972879577521319911431100000000000000), (980304935527/35900000000), (-6504993591085935104861473717777165199462650477001/1081730625945759155042639822862200000000000000)]
    bernstein := [(577923738573098380210829210805066351123765476622446862359/11893754013487730280449872703232978213404672000000000000000000), (82866352253304970749743823311770629511057390932508983299/1486719251685966285056234087904122276675584000000000000000000), (29730672519047884482010509184794701880082553908895055517/557519719382237356896087782964045853753344000000000000000000), (960730960383014416274999017572523438366468410397487979/23229988307593223204003657623501910573056000000000000000000), (57580676624499854377170615880108944476773983864911719/2903748538449152900500457202937738821632000000000000000000)]
    reserve := (19829773/1000000000000) }

theorem mixed_004_067_valid : mixed_004_067.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_067]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_067]
  · intro i; fin_cases i <;> norm_num [mixed_004_067]
  · norm_num [mixed_004_067]
  · norm_num [mixed_004_067, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_067, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_067, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_067, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_067]

def mixed_004_068 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/1280), (5/2048)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(1815773/12500000), (290527/2000000), (8491539/100000000), (14473771/100000000), (14473771/100000000), (16764583/100000000), (83719/500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(6951/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1120219/20000000), (359/100000000), (850329/20000000), (4240181/100000000), (1/100000000), (5596399/100000000), (1333/6250000)]
    alternative := .zero
    polynomial := [(-293501492735330441297257690424992884386081/8723402350517042293420177946325000000000000), (10217486369/359000000), (-26211483096490122375972411351682173877073448581/4361701175258521146710088973162500000000000), (10217486369/359000000), (-52422672691487509421503525445673922761262511081/8723402350517042293420177946325000000000000)]
    bernstein := [(1154518009057964357215966050418109224585590065255239/23416704878325140838055312666228948992000000000000000000), (422822163776275779413705503712543382141972798756461/7493345561064045068177700053193263677440000000000000000), (9710970381891462936731088238330416081937027429433509/179840293465537081636264801276638328258560000000000000000), (806017332912466692269816903042305657490704104766141/19182964636323955374534912136174755014246400000000000000), (3143728646428604248311153798807843237932963118269479/153463717090591642996279297089398040113971200000000000000)]
    reserve := (20485159/1000000000000) }

theorem mixed_004_068_valid : mixed_004_068.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_068]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_068]
  · intro i; fin_cases i <;> norm_num [mixed_004_068]
  · norm_num [mixed_004_068]
  · norm_num [mixed_004_068, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_068, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_068, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_068, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_068]

def mixed_004_069 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(5/2048), (13/5120)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(226999/1562500), (3632029/25000000), (8491937/100000000), (7236691/50000000), (7236691/50000000), (8381717/50000000), (4185453/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(18089/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2800503/50000000), (359/100000000), (4252081/100000000), (4240147/100000000), (1/100000000), (1119223/20000000), (1109/5000000)]
    alternative := .zero
    polynomial := [(-41012821237802075330569858322866019787317941/1124944534064646306524330449603650000000000000), (132902122789/4487500000), (-3378103350362438313223711122341927182899975017941/562472267032323153262165224801825000000000000), (132902122789/4487500000), (-6756165687903638824372091674825531499780162717941/1124944534064646306524330449603650000000000000)]
    bernstein := [(989631793807199600783359051379850060209570015981216219/19790233532914130273604365145475698328495718400000000000000), (5382036336195316356282816821702210103365743647287903/94239207299591096540973167359408087278551040000000000000), (20285743171959668865869692652070521926587044687160968609/371066878742139942630081846477669343659294720000000000000000), (25138918920690500751861705545808240945545028760885583/588995045622444353381082295996300545490944000000000000000), (16348109597683996164855333458934387244929758346245091899/773055997379458213812670513495144465956864000000000000000000)]
    reserve := (1057369/50000000000) }

theorem mixed_004_069_valid : mixed_004_069.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_069]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_069]
  · intro i; fin_cases i <;> norm_num [mixed_004_069]
  · norm_num [mixed_004_069]
  · norm_num [mixed_004_069, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_069, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_069, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_069, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_069]

def mixed_004_070 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(13/5120), (27/10240)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(1816211/12500000), (14529883/100000000), (1698467/20000000), (14472993/100000000), (14472993/100000000), (4190571/25000000), (1046239/6250000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(75203/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1400229/25000000), (359/100000000), (4252517/100000000), (4240113/100000000), (1/100000000), (5595831/100000000), (23031/100000000)]
    alternative := .zero
    polynomial := [(-1577700455344806420342336899122769784931109/40059624250180060796065847856975000000000000), (1104709984881/35900000000), (-120229847260890253749172651454692815046305931109/20029812125090030398032923928487500000000000), (1104709984881/35900000000), (-240458116821325162691924960572486507322826931109/40059624250180060796065847856975000000000000)]
    bernstein := [(1395770239087589141711099751677072594252758955224231051/27528764167131501316863126721315089678336000000000000000000), (3181882380728172782325625375672963486027479942291810829/55057528334263002633726253442630179356672000000000000000000), (18281593553090831733394940297295955445022996509653115473/330345170005578015802357520655781076140032000000000000000000), (9546758902056796560033295376313495886402626048368244989/220230113337052010534905013770520717426688000000000000000000), (9609234909169704558824093934917033003385743856644354731/440460226674104021069810027541041434853376000000000000000000)]
    reserve := (21816351/1000000000000) }

theorem mixed_004_070_valid : mixed_004_070.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_070]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_070]
  · intro i; fin_cases i <;> norm_num [mixed_004_070]
  · norm_num [mixed_004_070]
  · norm_num [mixed_004_070, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_070, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_070, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_070, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_070]

def mixed_004_071 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(27/10240), (7/2560)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(181643/1250000), (290633/2000000), (8492733/100000000), (3618151/25000000), (3618151/25000000), (16761133/100000000), (4184459/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1561/2000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5600827/100000000), (359/100000000), (4252953/100000000), (4240079/100000000), (1/100000000), (2797773/50000000), (11941/50000000)]
    alternative := .zero
    polynomial := [(-1712943824378886637395063026021270080893891293/40377837580779134476239848521412100000000000000), (286553262187/8975000000), (-121125677733728891578578120814598697543141000891293/20188918790389567238119924260706050000000000000), (286553262187/8975000000), (-242249642523633404270518846566171373816201107891293/40377837580779134476239848521412100000000000000)]
    bernstein := [(22821841516948592806569936397190203048299077873670809302387/443959019245174120383068770435734848611024896000000000000000000), (6490159070790822800635477332303391954217355869357003327167/110989754811293530095767192608933712152756224000000000000000000), (4662334383240746830926528708864643108045121665859155550641/83242316108470147571825394456700284114567168000000000000000000), (305269993107408403542162592768008177760607053299094767527/6936859675705845630985449538058357009547264000000000000000000), (38965317754873367957457037945651311337026384987950855107/1734214918926461407746362384514589252386816000000000000000000)]
    reserve := (22468563/1000000000000) }

theorem mixed_004_071_valid : mixed_004_071.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_071]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_071]
  · intro i; fin_cases i <;> norm_num [mixed_004_071]
  · norm_num [mixed_004_071]
  · norm_num [mixed_004_071, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_071, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_071, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_071, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_071]

def mixed_004_072 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(7/2560), (29/10240)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(1816649/12500000), (14533417/100000000), (8493131/100000000), (2894443/20000000), (2894443/20000000), (8379991/50000000), (16735849/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(40449/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2800369/50000000), (359/100000000), (425339/10000000), (848009/20000000), (1/100000000), (2797631/50000000), (24733/100000000)]
    alternative := .zero
    polynomial := [(-57176605200739864865741531869067642156108353/1254534504629687256831884892299150000000000000), (74233794253/2243750000), (-3761708901228035087820792839161636420590352608353/627267252314843628415942446149575000000000000), (74233794253/2243750000), (-7523360625850869435776719936791403773538549108353/1254534504629687256831884892299150000000000000)]
    bernstein := [(2807602766378426595479646919510905101575665374378326047/53881846690880673588008981824613314985984000000000000000000), (12750936877369989028466454178687706828163881307493593509/215527386763522694352035927298453259943936000000000000000000), (146604826560125445785414739681347632098193444034305445269/2586328641162272332224431127581439119327232000000000000000000), (154060887075211284180227946242370553456214782464218401181/3448438188216363109632574836775252159102976000000000000000000), (319113268169845638744128692647345933372425815668679532207/13793752752865452438530299347101008636411904000000000000000000)]
    reserve := (11567311/500000000000) }

theorem mixed_004_072_valid : mixed_004_072.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_072]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_072]
  · intro i; fin_cases i <;> norm_num [mixed_004_072]
  · norm_num [mixed_004_072]
  · norm_num [mixed_004_072, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_072, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_072, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_072, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_072]

def mixed_004_073 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(29/10240), (3/1024)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14534943/100000000), (2907037/20000000), (8493529/100000000), (578873/4000000), (578873/4000000), (16758831/100000000), (8366931/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(83747/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5600649/100000000), (359/100000000), (2126913/50000000), (4240011/100000000), (1/100000000), (2797489/50000000), (1599/6250000)]
    alternative := .zero
    polynomial := [(-178933951285436190708484829650174166329447/3663437174219668557967633932450000000000000), (1229293051111/35900000000), (-450198577621527037499295072762220736570434851077/75100462071503205438336495615225000000000000), (1229293051111/35900000000), (-69260755303927028624213161357417370461542322679/11553917241769723913590230094650000000000000)]
    bernstein := [(87185617846071471088622914078451750188890651764954638213/1651476625979364766294141917750470526369792000000000000000000), (9881912680618803189434930809024304650809143216813558171/165147662597936476629414191775047052636979200000000000000000), (5331166683499040456277410400842740923134961415177043/92953656246493326433066149216724419870720000000000000000), (14975881742659727837220736633968378922847581654021727/330295325195872953258828383550094105273958400000000000000), (157224619481950726571862920469122936991256028520397/6605906503917459065176567671001882105479168000000000000)]
    reserve := (5950153/250000000000) }

theorem mixed_004_073_valid : mixed_004_073.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_073]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_073]
  · intro i; fin_cases i <;> norm_num [mixed_004_073]
  · norm_num [mixed_004_073]
  · norm_num [mixed_004_073, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_073, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_073, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_073, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_073]

def mixed_004_074 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/1024), (31/10240)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(2907339/20000000), (14536953/100000000), (8493927/100000000), (2894287/20000000), (2894287/20000000), (209471/1250000), (26771/160000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(21649/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5600561/100000000), (359/100000000), (4254263/100000000), (4239977/100000000), (1/100000000), (5594693/100000000), (5287/20000000)]
    alternative := .zero
    polynomial := [(-16160434735919851156633770842569464740147429/309447730490154603765420014503286250000000000), (635427734119/17950000000), (-927182966458373775838371884741865331784226928679/154723865245077301882710007251643125000000000), (635427734119/17950000000), (-1854349772482011631825587135712888094103713709929/309447730490154603765420014503286250000000000)]
    bernstein := [(728027849469113708145197939339755693012280270916319/13609655114512753389120690360273511713551155200000000000), (5883411339356582595112551027520850093966498929947953/97211822246519667065147788287667940811079680000000000000), (5922733545873588211997773937510784266922669723354429613/102072413358845650418405177702051337851633664000000000000000), (2236029981928486132127587904164429768597507421381033549/48605911123259833532573894143833970405539840000000000000000), (83212309053551838393615852856276436012119821675723431191/3402413778628188347280172590068377928387788800000000000000000)]
    reserve := (4891369/200000000000) }

theorem mixed_004_074_valid : mixed_004_074.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_074]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_074]
  · intro i; fin_cases i <;> norm_num [mixed_004_074]
  · norm_num [mixed_004_074]
  · norm_num [mixed_004_074, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_074, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_074, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_074, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_074]

def mixed_004_075 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(31/10240), (1/320)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14538447/100000000), (7269361/50000000), (4247163/50000000), (2894209/20000000), (2894209/20000000), (1047283/6250000), (16729889/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(44723/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(700059/12500000), (359/100000000), (4254699/100000000), (4239943/100000000), (1/100000000), (699301/12500000), (5457/20000000)]
    alternative := .zero
    polynomial := [(-315028843543095053335088588375922604885247/5653984685603296338373868338650000000000000), (656221294157/17950000000), (-95967325255807286238210576397154545678371449733/16019623275876006292059293626175000000000000), (656221294157/17950000000), (-575798596044503484813356761876924883385945649199/96117739655256037752355761757050000000000000)]
    bernstein := [(19089349151040654170692681240912876859093199852657972507/352275241288334503810482639960488317812736000000000000000000), (2021318681580488957806843446888375412023131827004302991/33025803870781359732232747496295779794944000000000000000000), (20193180060893675347399752704380895482627492067047387/344018790320639163877424453086414372864000000000000000000), (88540097599557342303258356585024755110440184270943/1897162446621171859618149557461843968000000000000000000), (8439133569293296666386203499405604896600064051867/335955849922499183474047317467201536000000000000000000)]
    reserve := (25119769/1000000000000) }

theorem mixed_004_075_valid : mixed_004_075.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_075]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_075]
  · intro i; fin_cases i <;> norm_num [mixed_004_075]
  · norm_num [mixed_004_075]
  · norm_num [mixed_004_075, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_075, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_075, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_075, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_075]

def mixed_004_076 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/320), (33/10240)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(7270099/50000000), (14540491/100000000), (2123681/25000000), (7235327/50000000), (7235327/50000000), (134043/800000), (16727903/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(92297/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(43753/781250), (359/100000000), (132973/3125000), (4239909/100000000), (1/100000000), (5594123/100000000), (3517/12500000)]
    alternative := .zero
    polynomial := [(-330772408428336307111991723452369539356569/5575407890808653007240709774368000000000000), (1354054332181/35900000000), (-16695328055730813246354160381981248416505536569/2787703945404326503620354887184000000000000), (1354054332181/35900000000), (-33390325339053198156401208772239044463471716569/5575407890808653007240709774368000000000000)]
    bernstein := [(3208060721392700470382031788164615741804919912231/58462389045125741357204344923676999680000000000000000), (115767787792057668804909296962772644053517369609223/1870796449444023723430539037557663989760000000000000000), (10662651895196405363001986639063961382480630252381877/179596459146626277449331747605535743016960000000000000000), (90687933700541576546578163164144309735062888618555847/1915695564230680292792871974459047925514240000000000000000), (1580964401402268752646500099004305847832467490357891751/61302258055381769369371903182689533616455680000000000000000)]
    reserve := (1289483/50000000000) }

theorem mixed_004_076_valid : mixed_004_076.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_076]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_076]
  · intro i; fin_cases i <;> norm_num [mixed_004_076]
  · norm_num [mixed_004_076]
  · norm_num [mixed_004_076, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_076, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_076, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_076, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_076]

def mixed_004_077 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(33/10240), (17/5120)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(290839/2000000), (14542261/100000000), (4247561/50000000), (1808783/12500000), (1808783/12500000), (16754223/100000000), (16725917/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(95149/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1120059/20000000), (359/100000000), (4255573/100000000), (33919/800000), (1/100000000), (5593839/100000000), (14493/50000000)]
    alternative := .zero
    polynomial := [(-3296484092386438538657871064200139724819443/52283202148516423911053243354100000000000000), (279138160059/7180000000), (-156520532374705383182965589808953661945816569443/26141601074258211955526621677050000000000000), (279138160059/7180000000), (-313037768265318379927392521746843123751908319443/52283202148516423911053243354100000000000000)]
    bernstein := [(282653322199001909921047078549508971975983599420284669/5087255637137783518399345118484136722432000000000000000000), (5487591217595143489032106519272801312255120596574289/87711304088582474455161122732485115904000000000000000000), (38130412754615271561727564843961061949105272374854529/634970420099303612937178937837305724928000000000000000000), (118987081047139793254269999252626846030238977097322657/2477844340502454903358301717192704524288000000000000000000), (951154672976554414920464486238121764404556392468543597/35928742937285596098695374899294215602176000000000000000000)]
    reserve := (26473363/1000000000000) }

theorem mixed_004_077_valid : mixed_004_077.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_077]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_077]
  · intro i; fin_cases i <;> norm_num [mixed_004_077]
  · norm_num [mixed_004_077]
  · norm_num [mixed_004_077, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_077, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_077, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_077, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_077]

def mixed_004_078 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(17/5120), (7/2048)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14543701/100000000), (14544031/100000000), (53097/625000), (14469873/100000000), (14469873/100000000), (1675307/10000000), (4180983/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(98001/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5600207/100000000), (359/100000000), (425601/10000000), (26499/625000), (1/100000000), (5593553/100000000), (7459/25000000)]
    alternative := .zero
    polynomial := [(-6972626521404503791526255816059207065989/104244316094097731940061516920000000000000), (1437337365207/35900000000), (-312007096022975525240648914236207384882465989/52122158047048865970030758460000000000000), (1437337365207/35900000000), (-624007219419429645977506302216598710557865989/104244316094097731940061516920000000000000)]
    bernstein := [(4029504641019968607034396482248679055217038111647931/71636148546885794769654215583928103731200000000000000000), (604059469734576755698476929331950478939224071265647/9551486472918105969287228744523747164160000000000000000), (28601410378229299737809808405651504280161601255993/471032209623358650540192102469664243712000000000000000), (74401267175012893420815110892844523662251848570719/1528237835666896955085956599123799546265600000000000000), (49759488952257647509937706146996274059443841980699/1833885402800276346103147918948559455518720000000000000)]
    reserve := (3391671/125000000000) }

theorem mixed_004_078_valid : mixed_004_078.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_078]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_078]
  · intro i; fin_cases i <;> norm_num [mixed_004_078]
  · norm_num [mixed_004_078]
  · norm_num [mixed_004_078, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_078, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_078, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_078, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_078]

def mixed_004_079 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(7/2048), (9/2560)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(3636363/25000000), (7272901/50000000), (4247959/50000000), (7234741/50000000), (7234741/50000000), (4187979/25000000), (4180487/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(100853/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5600119/100000000), (9/2500000), (4256447/100000000), (2119903/50000000), (1/100000000), (1398317/25000000), (6137/20000000)]
    alternative := .zero
    polynomial := [(-444660154352756211112581745207777430909867/6294671289812023323439216887450000000000000), (739513785833/18000000000), (-18784943280743123441197607289996834205849859867/3147335644906011661719608443725000000000000), (739513785833/18000000000), (-37569441901331894126184101998248460634268809867/6294671289812023323439216887450000000000000)]
    bernstein := [(6305547399998922526722832152326668465145862289894997/110737028418817139350571691112237722972979200000000000000), (8842163514120121190169428356768380838657596894226907/138421285523521424188214613890297153716224000000000000000), (31834615150820674781736829667700055833004054569953503/519079820713205340705804802088614326435840000000000000000), (3553715897146720422720853399204484491638391875051113/72094419543500741764695111401196434227200000000000000000), (7507565586165392568999241448959639335307618622008213/270354073288127781617606667754486628352000000000000000000)]
    reserve := (13884691/500000000000) }

theorem mixed_004_079_valid : mixed_004_079.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_079]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_079]
  · intro i; fin_cases i <;> norm_num [mixed_004_079]
  · norm_num [mixed_004_079]
  · norm_num [mixed_004_079, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_079, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_079, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_079, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_079]

def mixed_004_080 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(9/2560), (37/10240)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(3636801/25000000), (14547573/100000000), (2124079/25000000), (14469091/100000000), (14469091/100000000), (8375381/50000000), (16719963/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(103707/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(175001/3125000), (359/100000000), (1064221/25000000), (1059943/25000000), (1/100000000), (5592983/100000000), (6307/20000000)]
    alternative := .zero
    polynomial := [(-2202927018330591534865899478037597320187189/29410114753838732117893028232200000000000000), (304138017309/7180000000), (-87992884466464097160528634276465644898255787189/14705057376919366058946514116100000000000000), (304138017309/7180000000), (-175983566005909863729522402653453252199191387189/29410114753838732117893028232200000000000000)]
    bernstein := [(72795888593580942190960731677283813711346618662688171/1263154810393444449044553726837036941312000000000000000000), (326417157288790873321192894261064884660344709033018303/5052619241573777796178214907348147765248000000000000000000), (537591320730231229600769077097207672418652387450641391/8661632985555047650591225555453967597568000000000000000000), (4043469514023792856731636568603066663672123967122638647/80841907865180444738851438517570364243968000000000000000000), (9202100990799066640563481719800099506466107620631673371/323367631460721778955405754070281456975872000000000000000000)]
    reserve := (28457087/1000000000000) }

theorem mixed_004_080_valid : mixed_004_080.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_080]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_080]
  · intro i; fin_cases i <;> norm_num [mixed_004_080]
  · norm_num [mixed_004_080]
  · norm_num [mixed_004_080, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_080, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_080, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_080, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_080]

def mixed_004_081 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(37/10240), (19/5120)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(2909791/20000000), (2909869/20000000), (1699343/20000000), (14468699/100000000), (14468699/100000000), (2093701/12500000), (16717979/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(106561/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(699993/12500000), (9/2500000), (2128661/50000000), (4239737/100000000), (1/100000000), (2796349/50000000), (253/781250)]
    alternative := .zero
    polynomial := [(-93993448326004279250110734663867470502011/1191844904013892733705197759200000000000000), (62497187897/1440000000), (-10666828641236345832854065641374962844246756033/1787767356020839100557796638800000000000000), (62497187897/1440000000), (-21333375302127713652870380950545934086082006033/3575534712041678201115593277600000000000000)]
    bernstein := [(2292573474692222900865332742036358952559445070008716287/39313419914065370272633814637899390386176000000000000000000), (183201495958049610548495636421099868720586737695628367/2808101422433240733759558188421385027584000000000000000000), (1848176940462610552541014431214818460355771753450488909/29485064935549027704475360978424542789632000000000000000000), (35550321682740264473883598639545828623852084435001023/702025355608310183439889547105346256896000000000000000000), (23845141892877391865510831046136889044670230014599669/819029581543028547346537804956237299712000000000000000000)]
    reserve := (5822779/200000000000) }

theorem mixed_004_081_valid : mixed_004_081.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_081]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_081]
  · intro i; fin_cases i <;> norm_num [mixed_004_081]
  · norm_num [mixed_004_081]
  · norm_num [mixed_004_081, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_081, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_081, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_081, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_081]

def mixed_004_082 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(19/5120), (39/10240)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(7275353/50000000), (14551117/100000000), (8497113/100000000), (3617077/25000000), (3617077/25000000), (8374227/50000000), (3343199/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(13677/12500000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(349991/6250000), (9/2500000), (4257759/100000000), (4239703/100000000), (1/100000000), (1398103/25000000), (33233/100000000)]
    alternative := .zero
    polynomial := [(-2440768269903924405417084886113705897641947/29355001158354526840686119919300000000000000), (66840022253/1500000000), (-262687857432814920925133958251474602754388700841/44032501737531790261029179878950000000000000), (66840022253/1500000000), (-525368392560820130077051665248290864391084475841/88065003475063580522058359757900000000000000)]
    bernstein := [(3570592828165481878868561095092156846763886298342056239/60517809575603908778064521882173276422144000000000000000000), (7978694382647732646544121682797558553880551153256421459/121035619151207817556129043764346552844288000000000000000000), (46011017725964606562151307093008562886531766692694736437/726213714907246905336774262586079317065728000000000000000000), (2760271169603164470439776619972433737814701201185313811/53793608511647918913835130561931801264128000000000000000000), (9613372290807443813716082048314141652689648227810937973/322761651069887513483010783371590807584768000000000000000000)]
    reserve := (29784741/1000000000000) }

theorem mixed_004_082_valid : mixed_004_082.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_082]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_082]
  · intro i; fin_cases i <;> norm_num [mixed_004_082]
  · norm_num [mixed_004_082]
  · norm_num [mixed_004_082, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_082, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_082, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_082, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_082]

def mixed_004_083 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(39/10240), (1/256)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14552457/100000000), (1455289/10000000), (8497511/100000000), (3616979/25000000), (3616979/25000000), (16747299/100000000), (4178503/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(7017/6250000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5599769/100000000), (9/2500000), (4258197/100000000), (4239669/100000000), (1/100000000), (5592127/100000000), (17041/50000000)]
    alternative := .zero
    polynomial := [(-4016129436368271849123098149938048509863111/45875479947911802603572453433900000000000000), (3428991989/75000000), (-136825708522731906856844046565950484384458238111/22937739973955901301786226716950000000000000), (3428991989/75000000), (-273647400916027445441838970033751030720406613111/45875479947911802603572453433900000000000000)]
    bernstein := [(30102574186821104475454348702780726900948458539529983849/504406236325337537727363431078613498200064000000000000000000), (119971013180631746496604682193660652345658031964696793/1801450844019062634740583682423619636428800000000000000000), (60560232472259456021601275352204770821177990232060651/945761693110007883238806433272400309125120000000000000000), (58534128946110182317241363668562194070416469545321/1125906777511914146712864801514762272768000000000000000), (6002099789858686768784332999722038608927441884041/197033686064584975674751340265083397734400000000000000)]
    reserve := (15231151/500000000000) }

theorem mixed_004_083_valid : mixed_004_083.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_083]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_083]
  · intro i; fin_cases i <;> norm_num [mixed_004_083]
  · norm_num [mixed_004_083]
  · norm_num [mixed_004_083, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_083, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_083, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_083, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_083]

def mixed_004_084 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/256), (41/10240)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(454819/3125000), (14554663/100000000), (8497909/100000000), (3616881/25000000), (3616881/25000000), (16746143/100000000), (16712029/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(14391/12500000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5599681/100000000), (9/2500000), (2129317/50000000), (2119817/50000000), (1/100000000), (5591841/100000000), (3493/10000000)]
    alternative := .zero
    polynomial := [(-114571563121028481061187739543688326883997/1244599643228169671199423342900000000000000), (23440026427/500000000), (-3711717142235567508825342815882682489544233997/622299821614084835599711671450000000000000), (23440026427/500000000), (-353491414900381618531886878286943870988646857/59266649677531889104734444900000000000000)]
    bernstein := [(322702410861656138430843576012174439261374399107/5345514764278256603740596351814493798400000000000000), (14385404797549402028332963511679946383649448752891/213820590571130264149623854072579751936000000000000000), (1660274619891687882788266025656599824295031835400857/25658470868535631697954862488709570232320000000000000000), (18013992373458077149885207385916115343485990925821483/342112944913808422639398166516127603097600000000000000000), (425905445043378611021447014874734282892975803113286883/13684517796552336905575926660645104123904000000000000000000)]
    reserve := (778079/25000000000) }

theorem mixed_004_084_valid : mixed_004_084.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_084]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_084]
  · intro i; fin_cases i <;> norm_num [mixed_004_084]
  · norm_num [mixed_004_084]
  · norm_num [mixed_004_084, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_084, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_084, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_084, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_084]

def mixed_004_085 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(41/10240), (21/5120)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(7277979/50000000), (14556437/100000000), (2124577/25000000), (3616783/25000000), (3616783/25000000), (4186247/25000000), (8355023/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(23597/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2799797/50000000), (9/2500000), (16637/390625), (10599/250000), (1/100000000), (1118311/20000000), (35779/100000000)]
    alternative := .zero
    polynomial := [(-9167238906846706767846143972041609690141/94819679908240124075281243200000000000000), (345894490513/7200000000), (-282753898882411534273517887939626681689290141/47409839954120062037640621600000000000000), (345894490513/7200000000), (-565498630525916221840267929735281321768890141/94819679908240124075281243200000000000000)]
    bernstein := [(11241922285002135094587334877114584882079748494559/184164177002487866344265476904845312000000000000000000), (231499958670101416269429753523542797433720102433023/3407037274546025527368911322739638272000000000000000000), (51115869903060421783486411008464373322092607565508017/781915054508312858531165148568746983424000000000000000000), (6948378510551555440988880864375646616024974951464959/130319175751385476421860858094791163904000000000000000000), (2071036244029676003822487082844280902637310331515379/65159587875692738210930429047395581952000000000000000000)]
    reserve := (31784059/1000000000000) }

theorem mixed_004_085_valid : mixed_004_085.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_085]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_085]
  · intro i; fin_cases i <;> norm_num [mixed_004_085]
  · norm_num [mixed_004_085]
  · norm_num [mixed_004_085, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_085, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_085, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_085, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_085]

def mixed_004_086 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(21/5120), (43/10240)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14557709/100000000), (14558211/100000000), (4249353/50000000), (14466739/100000000), (14466739/100000000), (2092979/12500000), (522127/3125000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(60421/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5599507/100000000), (9/2500000), (425951/10000000), (847913/20000000), (1/100000000), (5591269/100000000), (36627/100000000)]
    alternative := .zero
    polynomial := [(-98448008104628221639074535988037524298131/970697136298410295235636472850781250000000), (98404063319/2000000000), (-92622273338696872784515685153884070932000287067/15531154180774564723770183565612500000000000), (98404063319/2000000000), (-92620698170567198732969459961308262331611516971/15531154180774564723770183565612500000000000)]
    bernstein := [(658896763407741459618175380553509587007381703691726149/10672927884089668389956513957475577233408000000000000000000), (1464938323444034863668595212701430831232634054492553467/21345855768179336779913027914951154466816000000000000000000), (8458480766571582134725850989550304724866141007376392783/128075134609076020679478167489706926800896000000000000000000), (4608874792172370830601566385981585300189028277982096763/85383423072717347119652111659804617867264000000000000000000), (5538830247870863679942765156070417848601018317928207429/170766846145434694239304223319609235734528000000000000000000)]
    reserve := (8108761/250000000000) }

theorem mixed_004_086_valid : mixed_004_086.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_086]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_086]
  · intro i; fin_cases i <;> norm_num [mixed_004_086]
  · norm_num [mixed_004_086]
  · norm_num [mixed_004_086, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_086, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_086, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_086, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_086]

def mixed_004_087 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(43/10240), (11/2560)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(727973/5000000), (2911997/20000000), (265597/3125000), (14466347/100000000), (14466347/100000000), (669707/4000000), (8353041/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(123701/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(279971/5000000), (9/2500000), (1064987/25000000), (4239531/100000000), (1/100000000), (5590983/100000000), (1499/4000000)]
    alternative := .zero
    polynomial := [(-1501198936201818349201243398309033812207/14125496160718805374069591572000000000000), (72524523341/1440000000), (-42117545690809116730787213903256344850022207/7062748080359402687034795786000000000000), (72524523341/1440000000), (-9359287798075781293691691840346042296248023/1569499573413200597118843508000000000000)]
    bernstein := [(3231482374759772147880874070975677766069554620587531/51770490922718574023524644036110702346240000000000000000), (2691348498861178757867130027498031929219456341645761/38827868192038930517643483027083026759680000000000000000), (277613218533870315285440677414653966021103728887813/4160128734861313984033230324330324295680000000000000000), (132670997077025061515662702919975088718399381210369/2426741762002433157352717689192689172480000000000000000), (20099777630458666498517057775185098942856497098913/606685440500608289338179422298172293120000000000000000)]
    reserve := (8282619/250000000000) }

theorem mixed_004_087_valid : mixed_004_087.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_087]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_087]
  · intro i; fin_cases i <;> norm_num [mixed_004_087]
  · norm_num [mixed_004_087]
  · norm_num [mixed_004_087, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_087, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_087, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_087, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_087]

def mixed_004_088 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(11/2560), (9/2048)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14561211/100000000), (91011/625000), (8499503/100000000), (7232977/50000000), (14465953/100000000), (16741519/100000000), (167041/1000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(791/625000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5599333/100000000), (9/2500000), (2130193/50000000), (529937/12500000), (1/100000000), (5590697/100000000), (38323/100000000)]
    alternative := .zero
    polynomial := [(-10430038818645425923245753905079328216442881/93757086692287709088906499149900000000000000), (386450687/7500000), (-279541799691850111933768753570892657392828442881/46878543346143854544453249574950000000000000), (386450687/7500000), (-559073169344881578441614261387880235457440442881/93757086692287709088906499149900000000000000)]
    bernstein := [(254079085592931005733018218487274856432972016566992079/4026836211116125259596153702506723016704000000000000000000), (32209010776857064933748844642156146877974314454981603/460209852698985743953846137429339773337600000000000000000), (521110756938604719539286619657304292864752899776929573/7731525525342960498424615108812908192071680000000000000000), (3259656230565147240666191978469332349860842162140911/58906861145470175226092305590955490987212800000000000000), (2229492523420948877379811096727826021784666710167351/65975684482926596253223382261870149905678336000000000000)]
    reserve := (33792639/1000000000000) }

theorem mixed_004_088_valid : mixed_004_088.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_088]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_088]
  · intro i; fin_cases i <;> norm_num [mixed_004_088]
  · norm_num [mixed_004_088]
  · norm_num [mixed_004_088, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_088, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_088, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_088, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_088]

def mixed_004_089 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(9/2048), (23/5120)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14562961/100000000), (910221/6250000), (8499901/100000000), (14465561/100000000), (14465561/100000000), (16740361/100000000), (417553/2500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(129419/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5599247/100000000), (9/2500000), (532603/12500000), (4239461/100000000), (1/100000000), (5590411/100000000), (39171/100000000)]
    alternative := .zero
    polynomial := [(-96618268956446984160982386126619455171144473/830564816735695783245761074524300000000000000), (39517162333/750000000), (-2476308630688414736815000420386031158861608544473/415282408367847891622880537262150000000000000), (39517162333/750000000), (-4952520643107873026645839858385935698268045944473/830564816735695783245761074524300000000000000)]
    bernstein := [(37281337699631080007282198200840173041769223782869983/584458031118425598336311057729402840234852352000000000000), (516284540857781605802997690861630255585522952601849093/7305725388980319979203888221617535502935654400000000000000), (18649117336809940174366453030184038564624588988548330261/273964702086761999220145808310657581360087040000000000000000), (12784137404714012323992108782795090568673506959288172761/228303918405634999350121506925547984466739200000000000000000), (19658769698244106109923617499036905864179891181893601607/570759796014087498375303767313869961166848000000000000000000)]
    reserve := (34443157/1000000000000) }

theorem mixed_004_089_valid : mixed_004_089.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_089]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_089]
  · intro i; fin_cases i <;> norm_num [mixed_004_089]
  · norm_num [mixed_004_089]
  · norm_num [mixed_004_089, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_089, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_089, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_089, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_089]

def mixed_004_090 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(23/5120), (47/10240)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(1820589/12500000), (227583/1562500), (8500299/100000000), (904073/6250000), (14465167/100000000), (4184801/25000000), (8350069/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(3307/2500000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(139979/2500000), (9/2500000), (2130631/50000000), (4239427/100000000), (1/100000000), (44721/800000), (20009/50000000)]
    alternative := .zero
    polynomial := [(-202201691766913516267411619386947766291/1663819719827444444927744775000000000000), (1346335813/25000000), (-84329615757663302461067352526680050979126947/14142467618533277781885830587500000000000), (1346335813/25000000), (-168655794086566567392358159055830523846226947/28284935237066555563771661175000000000000)]
    bernstein := [(1252944345560126095187652193918537138136802470870173/19437259490028618099482580345314869248000000000000000000), (132069335280721350747119672684760739303237321496657/1851167570478916009474531461458558976000000000000000000), (16035491473221305167257898528361645657380445005113799/233247113880343417193790964143778430976000000000000000000), (419669680516517340608917459731242614515736303657697/7404670281915664037898125845834235904000000000000000000), (10924058152031407976730362557060057525356255639186493/310996151840457889591721285525037907968000000000000000000)]
    reserve := (35126023/1000000000000) }

theorem mixed_004_090_valid : mixed_004_090.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_090]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_090]
  · intro i; fin_cases i <;> norm_num [mixed_004_090]
  · norm_num [mixed_004_090]
  · norm_num [mixed_004_090, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_090, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_090, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_090, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_090]

def mixed_004_091 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(47/10240), (3/640)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(7283231/50000000), (1456709/10000000), (8500699/100000000), (578591/4000000), (14464773/100000000), (4184511/25000000), (16698157/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(135141/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5599073/100000000), (9/2500000), (4261701/100000000), (132481/3125000), (1/100000000), (2794919/50000000), (8173/20000000)]
    alternative := .zero
    polynomial := [(-161637011371830147704131839662111189280551/1274311968790535373293263062900000000000000), (66021126091/1200000000), (-3799260265952569974818831753476369088917430551/637155984395267686646631531450000000000000), (66021126091/1200000000), (-2532786298297922706496653125037692022215193517/424770656263511791097754354300000000000000)]
    bernstein := [(912370984905358097884860822716745172437892283078438969/14011208270993208582721834681037544751104000000000000000000), (21015630535229590667252859335286159434670221450325527/291900172312358512140038222521615515648000000000000000000), (11394560880311029311021745383934660519072975940201507/164193846925701663078771500168408727552000000000000000000), (17825097557475356218211823705772959925311846744071/310973194935041028558279356379561984000000000000000000), (7646564967949768175686555925642666743770641402569/213794071517840707133817057510948864000000000000000000)]
    reserve := (35766029/1000000000000) }

theorem mixed_004_091_valid : mixed_004_091.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_091]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_091]
  · intro i; fin_cases i <;> norm_num [mixed_004_091]
  · norm_num [mixed_004_091]
  · norm_num [mixed_004_091, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_091, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_091, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_091, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_091]

def mixed_004_092 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/640), (49/10240)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(3642053/25000000), (14568867/100000000), (8501097/100000000), (14464381/100000000), (723219/5000000), (3347377/20000000), (16696177/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(138003/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5598987/100000000), (9/2500000), (213107/5000000), (2119679/50000000), (1/100000000), (5589551/100000000), (41713/100000000)]
    alternative := .zero
    polynomial := [(-4679993637016878727753847701713168238663583/35381551302759781830889156019580000000000000), (224729844449/4000000000), (-105487915152572267140321723036697067556089973583/17690775651379890915444578009790000000000000), (224729844449/4000000000), (-210971150311507517401915692225692421943941283583/35381551302759781830889156019580000000000000)]
    bernstein := [(390645487126311258483823979890463118829918968407377/5936039286214822558897028425981938892800000000000000000), (6903612717303628300550888624459922832727339154670891/94976628579437160942352454815711022284800000000000000000), (319523265409764115147397055518203765709966635739686459/4558878171812983725232917831154129069670400000000000000000), (1410481280074580113103224251346157999119167896277304499/24314016916335913201242228432822021704908800000000000000000), (14182337939995461411861413135968076410198561115668756417/389024270661374611219875654925152347278540800000000000000000)]
    reserve := (36456177/1000000000000) }

theorem mixed_004_092_valid : mixed_004_092.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_092]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_092]
  · intro i; fin_cases i <;> norm_num [mixed_004_092]
  · norm_num [mixed_004_092]
  · norm_num [mixed_004_092, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_092, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_092, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_092, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_092]

def mixed_004_093 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(49/10240), (5/1024)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(7284981/50000000), (14570643/100000000), (1700299/20000000), (7231993/50000000), (7231993/50000000), (1045983/6250000), (16694199/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(28173/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5598901/100000000), (9/2500000), (2131289/50000000), (2119661/50000000), (1/100000000), (1117853/20000000), (42559/100000000)]
    alternative := .zero
    polynomial := [(-646493553946481392049922694301765737737/4691010676281718319710569775000000000000), (9175615331/160000000), (-13986179968698272526403624055176986699343987/2345505338140859159855284887500000000000), (9175615331/160000000), (-27971713443842598571415198187659671632950237/4691010676281718319710569775000000000000)]
    bernstein := [(3430774461041794772901572439880456863638347303409763/51578207845931067048552881585026760704000000000000000000), (3984376017486818475264198638183117273105091610177/54292850364137965314266191142133432320000000000000000), (109520636454579590509995751133996778991214256759713/1547346235377932011456586447550802821120000000000000000), (31867008155104358820150046998645847398419792377/542928503641379653142661911421334323200000000000000), (191519018546014023891765144648625679965799893363/5157820784593106704855288158502676070400000000000000)]
    reserve := (3713177/100000000000) }

theorem mixed_004_093_valid : mixed_004_093.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_093]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_093]
  · intro i; fin_cases i <;> norm_num [mixed_004_093]
  · norm_num [mixed_004_093]
  · norm_num [mixed_004_093, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_093, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_093, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_093, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_093]

def mixed_004_094 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(5/1024), (51/10240)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14571713/100000000), (14572421/100000000), (8501893/100000000), (1807949/12500000), (1807949/12500000), (16734569/100000000), (16692219/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(8983/6250000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1119763/20000000), (9/2500000), (4263017/100000000), (529911/12500000), (1/100000000), (2794489/50000000), (21703/50000000)]
    alternative := .zero
    polynomial := [(-200101494995973059208076389665255385323183/1394683304654591981277100805700000000000000), (65827603849/1125000000), (-4158330176757084310335164839398453256280435683/697341652327295990638550402850000000000000), (65827603849/1125000000), (-2772153417339724215870373867469080419058516061/464894434884863993759033601900000000000000)]
    bernstein := [(103058016142809231004314960038481131499546177984217/1533470510532781346767102022189248099123200000000000000), (227176187646516174791520368697723906654737210446451/3066941021065562693534204044378496198246400000000000000), (32875129240289381150142589789024507794611151733819067/460041153159834404030130606656774429736960000000000000000), (187721662649893130073377013651407494923242162030083/3161794867077899684055880458122161029120000000000000000), (5976474129235272444980218896813907817326894520939161/158089743353894984202794022906108051456000000000000000000)]
    reserve := (4725539/125000000000) }

theorem mixed_004_094_valid : mixed_004_094.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_094]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_094]
  · intro i; fin_cases i <;> norm_num [mixed_004_094]
  · norm_num [mixed_004_094]
  · norm_num [mixed_004_094, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_094, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_094, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_094, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_094]

def mixed_004_095 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(51/10240), (13/2560)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14573463/100000000), (72871/500000), (2125573/25000000), (7231599/50000000), (7231599/50000000), (1673341/10000000), (52157/312500)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(4581/3125000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(559873/10000000), (9/2500000), (133233/3125000), (4239253/100000000), (1/100000000), (1397173/25000000), (44253/100000000)]
    alternative := .zero
    polynomial := [(-10880221521685151392917625134406415519/72899541333922980115645965000000000000), (37299967/625000), (-652084278650440277844409346723599319621557/109349312000884470173468947500000000000), (37299967/625000), (-1304135916636315500234639940571795419996557/218698624001768940346937895000000000000)]
    bernstein := [(365169524994989831006318524719666751459804333469/5379455929945332230521260114287001600000000000000000), (14978467635658370218016302576984100101211529527903/200384733390463625586916939257190809600000000000000000), (32523837029589141239260984562458961207066546650601/450865650128543157570563113328679321600000000000000000), (205095599665447174461894572534503093643500625911/3415648864610175436140629646429388800000000000000000), (361414418928719230456977551442889763507006757923/9393034377677982449386731527680819200000000000000000)]
    reserve := (19238427/500000000000) }

theorem mixed_004_095_valid : mixed_004_095.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_095]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_095]
  · intro i; fin_cases i <;> norm_num [mixed_004_095]
  · norm_num [mixed_004_095]
  · norm_num [mixed_004_095, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_095, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_095, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_095, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_095]

def mixed_004_096 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(13/2560), (53/10240)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14575213/100000000), (14575979/100000000), (850269/10000000), (14462803/100000000), (14462803/100000000), (66929/400000), (8344131/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(149457/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1399661/25000000), (9/2500000), (852779/20000000), (2119609/50000000), (1/100000000), (1117681/20000000), (45099/100000000)]
    alternative := .zero
    polynomial := [(-9892250426227490732221012815989249048509/63763169770564568322478701574500000000000), (730165880681/12000000000), (-126751807374272858838609489911577484883030131/21254389923521522774159567191500000000000), (730165880681/12000000000), (-95061382468098087256274062180479116350010471/15940792442641142080619675393625000000000)]
    bernstein := [(5215609667447720684396493645417754803481740849441/76072424681630734555945445810839224320000000000000000), (206572802144915600925687658945804423076634809502289/2738607288538706444014036049190212075520000000000000000), (797699619071761913598580764689599839851794866574009/10954429154154825776056144196760848302080000000000000000), (2661091479326322621505804085171150111255688818380129/43817716616619303104224576787043393208320000000000000000), (762685868729942350073060447482908912692908652048961/19474540718497468046322034127574841425920000000000000000)]
    reserve := (39163227/1000000000000) }

theorem mixed_004_096_valid : mixed_004_096.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_096]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_096]
  · intro i; fin_cases i <;> norm_num [mixed_004_096]
  · norm_num [mixed_004_096]
  · norm_num [mixed_004_096, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_096, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_096, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_096, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_096]

def mixed_004_097 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(53/10240), (27/5120)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14576963/100000000), (7288879/50000000), (8503089/100000000), (14462409/100000000), (14462409/100000000), (1673109/10000000), (16686283/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(76161/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2799279/50000000), (9/2500000), (2132167/50000000), (4239183/100000000), (1/100000000), (2794059/50000000), (9189/20000000)]
    alternative := .zero
    polynomial := [(-2153948643060672723621927654143129084671/13366482164107252465797017415000000000000), (186043948153/3000000000), (-39857836482644796414670012143235246212783421/6683241082053626232898508707500000000000), (186043948153/3000000000), (-79713519016646532156616402358816349296482171/13366482164107252465797017415000000000000)]
    bernstein := [(10177400632182431193796666208156444782544056762072949/146966025618964363205154683831724697190400000000000000000), (27552395578939433782942187858349858427156085518897/361985284775774293608755378895873638400000000000000000), (623193071509366369106858360975192110792907351921339/8478809170324867107989693297984117145600000000000000000), (5557032286166298475768259177322769531843378256657/90496321193943573402188844723968409600000000000000000), (365880750141491422783266049478503393795831086222389/9185376601185272700322167739482793574400000000000000000)]
    reserve := (39832961/1000000000000) }

theorem mixed_004_097_valid : mixed_004_097.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_097]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_097]
  · intro i; fin_cases i <;> norm_num [mixed_004_097]
  · norm_num [mixed_004_097]
  · norm_num [mixed_004_097, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_097, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_097, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_097, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_097]

def mixed_004_098 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(27/5120), (11/2048)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(1822339/12500000), (7289769/50000000), (8503487/100000000), (7231007/50000000), (7231007/50000000), (16729929/100000000), (3336861/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(38797/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5598473/100000000), (9/2500000), (4264773/100000000), (1059787/25000000), (1/100000000), (5587831/100000000), (46791/100000000)]
    alternative := .zero
    polynomial := [(-12295798369424644785616598893543661268266323/73510127518928275525440955448700000000000000), (94774251781/1500000000), (-219213810444614281997492510258048015489123366323/36755063759464137762720477724350000000000000), (94774251781/1500000000), (-438415325090859139350199403917202487316978466323/73510127518928275525440955448700000000000000)]
    bernstein := [(3532350440257750208770321063457623707600193686374108957/50515774978973850296231379140985520914432000000000000000000), (1551635539955934418027339079701268013519244624001399981/20206309991589540118492551656394208365772800000000000000000), (1798534915486721401524126971166814322903150679139167671/24247571989907448142191061987673050038927360000000000000000), (8027971522204273333477121384749331788417458766205653/129320383946173056758352330600922933540945920000000000000), (83805142702522192602349098936452938378444510383533/2069126143138768908133637289614766936655134720000000000)]
    reserve := (20251337/500000000000) }

theorem mixed_004_098_valid : mixed_004_098.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_098]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_098]
  · intro i; fin_cases i <;> norm_num [mixed_004_098]
  · norm_num [mixed_004_098]
  · norm_num [mixed_004_098, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_098, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_098, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_098, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_098]

def mixed_004_099 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(11/2048), (7/1280)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(7290231/50000000), (14581319/100000000), (4251943/50000000), (14461619/100000000), (14461619/100000000), (261387/1562500), (2085291/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(31611/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5598387/100000000), (9/2500000), (4265213/100000000), (4239113/100000000), (1/100000000), (698443/12500000), (47637/100000000)]
    alternative := .zero
    polynomial := [(-3246321724578402713531499220311488280215773/18710332345824238256025271784850000000000000), (154444110047/2400000000), (-55799374651040205586933411952115230888487928273/9355166172912119128012635892425000000000000), (154444110047/2400000000), (-111595502980355832771153292405010150288695640773/18710332345824238256025271784850000000000000)]
    bernstein := [(37182769812046777421690036147535429023096559599483/526649036128951110688706509310802645913436160000000000), (212494682764902869669418944957565620126578647172981/2742963729838287034837013069327097114132480000000000000), (28873790505460319741447038727721469208771955815611481/385729274508509114273954962874123031674880000000000000000), (1681155936075365986743489893405047265811428292555397/26786755174202021824580205755147432755200000000000000000), (2068570800489942731995035630537040334099894728270427/50225165951628790921087885790901436416000000000000000000)]
    reserve := (20592971/500000000000) }

theorem mixed_004_099_valid : mixed_004_099.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_099]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_099]
  · intro i; fin_cases i <;> norm_num [mixed_004_099]
  · norm_num [mixed_004_099]
  · norm_num [mixed_004_099, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_099, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_099, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_099, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_099]

def mixed_004_100 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(7/1280), (57/10240)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(3645553/25000000), (145831/1000000), (2126071/25000000), (14461223/100000000), (14461223/100000000), (16727607/100000000), (16680351/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(80461/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2799151/50000000), (9/2500000), (1066413/25000000), (2119539/50000000), (1/100000000), (698407/12500000), (24241/50000000)]
    alternative := .zero
    polynomial := [(-1926535002577060593559126075362244711448413/10711549151852630488961174415900000000000000), (58968786773/900000000), (-3549666356109824713232622812731801892429133157/595086063991812804942287467550000000000000), (58968786773/900000000), (-63892067874974267777593651503097071819012948413/10711549151852630488961174415900000000000000)]
    bernstein := [(2049868082041338878868614831266216743924214291378787/28753595810439741101037958206276501504000000000000000000), (1997489223732848980570468083820877213541576627856693/25558751831501992089811518405579112448000000000000000000), (138999584380696113671963073733111379139812279875362787/1840230131868143430466429325201696096256000000000000000000), (311286960624218224403757783463599097484142757175880479/4907280351648382481243811533871189590016000000000000000000), (4929169461648122379781680493517077282577476064899321187/117774728439561179549851476812908550160384000000000000000000)]
    reserve := (20926261/500000000000) }

theorem mixed_004_100_valid : mixed_004_100.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_100]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_100]
  · intro i; fin_cases i <;> norm_num [mixed_004_100]
  · norm_num [mixed_004_100]
  · norm_num [mixed_004_100, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_100, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_100, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_100, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_100]

def mixed_004_101 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(57/10240), (29/5120)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(7291981/50000000), (14584881/100000000), (8504683/100000000), (3615207/25000000), (3615207/25000000), (3345289/20000000), (8339187/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(16379/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5598217/100000000), (9/2500000), (1066523/25000000), (4239043/100000000), (1/100000000), (5586969/100000000), (49327/100000000)]
    alternative := .zero
    polynomial := [(-4104073254390835320296153531981111206846157/22026545494903439938531220070060000000000000), (80028869609/1200000000), (-65698685336002460991822084602773740112206781157/11013272747451719969265610035030000000000000), (80028869609/1200000000), (-131393266598750531148323873052015499113206716157/22026545494903439938531220070060000000000000)]
    bernstein := [(17432498230273011043289175428640299073942930685131358243/242184428913834007587563111618269513619865600000000000000000), (9547042054484484548938192749045635791370131937870116271/121092214456917003793781555809134756809932800000000000000000), (13844502228673820281646344999952711199930968962230173761/181638321685375505690672333713702135214899200000000000000000), (1941031386149858552988812137972033568407809963500066839/30273053614229250948445388952283689202483200000000000000000), (643801537600906886996066489430268674662799552423975283/15136526807114625474222694476141844601241600000000000000000)]
    reserve := (2658311/62500000000) }

theorem mixed_004_101_valid : mixed_004_101.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_101]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_101]
  · intro i; fin_cases i <;> norm_num [mixed_004_101]
  · norm_num [mixed_004_101]
  · norm_num [mixed_004_101, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_101, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_101, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_101, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_101]

def mixed_004_102 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(29/5120), (3/512)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(7293293/50000000), (7293777/50000000), (8505281/100000000), (7230117/50000000), (7230117/50000000), (8362351/50000000), (16675409/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(168093/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(559809/10000000), (9/1250000), (4266751/100000000), (423899/10000000), (1/100000000), (5586537/100000000), (10199/20000000)]
    alternative := .zero
    polynomial := [(-73078178029208367576141793008636719309/744481958450405581050036700000000000000), (137559905749/4000000000), (-3361559700083876608555036518503302771582927/1116722937675608371575055050000000000000), (137559905749/4000000000), (-6722900165633665592007344611627579633007927/2233445875351216743150110100000000000000)]
    bernstein := [(89484541124656018824321387567401723457023900581913/1534812318723130948101976783727886336000000000000000000), (11130565686124956174983530870758644704803436933511/153481231872313094810197678372788633600000000000000000), (3112591920259294236484148896318976850530225857163/46044369561693928443059303511836590080000000000000000), (22275555305721756221634990042503359652494263021/511604106241043649367325594575962112000000000000000), (17545307141476330138145216728146627713997619/51160410624104364936732559457596211200000000000000)]
    reserve := (171473/500000000000) }

theorem mixed_004_102_valid : mixed_004_102.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_102]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_102]
  · intro i; fin_cases i <;> norm_num [mixed_004_102]
  · norm_num [mixed_004_102]
  · norm_num [mixed_004_102, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_102, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_102, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_102, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_102]

def mixed_004_103 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/512), (31/5120)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(2918017/20000000), (182389/1250000), (4253039/50000000), (7229721/50000000), (7229721/50000000), (2090297/12500000), (8335729/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(173833/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5597921/100000000), (721/100000000), (4267631/100000000), (105973/2500000), (1/100000000), (2792981/50000000), (13171/25000000)]
    alternative := .zero
    polynomial := [(-5387086666849801030943313784464590520502247/51388511574884338152819463354387500000000000), (640114601349/18025000000), (-77231050061385333934885359177550536577358752247/25694255787442169076409731677193750000000000), (640114601349/18025000000), (-154456713036103818068739775041316608564197002247/51388511574884338152819463354387500000000000)]
    bernstein := [(30124658657398318885433167606468776712845226273711/504484517952561571083347760684262332825600000000000000), (2608705894852856450260961882193679894306249408986397/35313916256679309975834343247898363297792000000000000000), (73014948452969256891242039252456617468432646784292483/1059417487700379299275030297436950898933760000000000000000), (158410096897755763904993596107117751561209148887975989/3531391625667930997583434324789836329779200000000000000000), (8501643464744231558720531625073819253008547321336959/5044845179525615710833477606842623328256000000000000000000)]
    reserve := (1685213/1000000000000) }

theorem mixed_004_103_valid : mixed_004_103.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_103]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_103]
  · intro i; fin_cases i <;> norm_num [mixed_004_103]
  · norm_num [mixed_004_103]
  · norm_num [mixed_004_103, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_103, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_103, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_103, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_103]

def mixed_004_104 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(31/5120), (1/160)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14593583/100000000), (114021/781250), (2126719/25000000), (1807331/12500000), (1807331/12500000), (16720049/100000000), (4166877/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(22447/12500000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(699719/12500000), (721/100000000), (133391/3125000), (4238849/100000000), (1/100000000), (2792693/50000000), (13593/25000000)]
    alternative := .zero
    polynomial := [(-614919097146238313460689321296174534867003/5496746304338497035708490169700000000000000), (3209818251/87500000), (-8260381484156892057022081440366723399057367003/2748373152169248517854245084850000000000000), (3209818251/87500000), (-16520148049216637875730702191412150623579867003/5496746304338497035708490169700000000000000)]
    bernstein := [(230853244131778698312580955479582104991030001845612037/3777335297846833229145745514943838420992000000000000000000), (2961180164869174763460732061014824697615693644593609/39347242685904512803601515780664983552000000000000000000), (777870583212331924934258219871100486806040082879951/11066412005410644226012926313312026624000000000000000000), (77210613675025315202885743045500902947837204703/1670653986324070686294221967589376000000000000000000), (10920798851272515544084180529715824827023499397/3602347658011277417321916117614592000000000000000000)]
    reserve := (1515789/500000000000) }

theorem mixed_004_104_valid : mixed_004_104.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_104]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_104]
  · intro i; fin_cases i <;> norm_num [mixed_004_104]
  · norm_num [mixed_004_104]
  · norm_num [mixed_004_104, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_104, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_104, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_104, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_104]

def mixed_004_105 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/160), (33/5120)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14597081/100000000), (7299129/50000000), (8507673/100000000), (7228927/50000000), (7228927/50000000), (417943/2500000), (16663559/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(92661/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(349849/6250000), (721/100000000), (266837/6250000), (2119389/50000000), (1/100000000), (558481/10000000), (2803/5000000)]
    alternative := .zero
    polynomial := [(-76014896841866624884634675508316123810367/638022629886714025029507645060000000000000), (1364703610577/36050000000), (-958768247435836531362054282195336337572610367/319011314943357012514753822530000000000000), (1364703610577/36050000000), (-273922925710690170871317704245023479860201481/91146089983816289289929663580000000000000)]
    bernstein := [(26138984088591449350136801525512189971514679233/418134510722556903443338130266521600000000000000000), (1025523504316467943253614974393140857507150929889/13380304343121820910186820168528691200000000000000000), (92057130887091536820950514861001192814045850308611/1284509216939694807377934736178754355200000000000000000), (651941262396937621372120150940343406859750516953121/13701431647356744612031303852573379788800000000000000000), (1924180990673286815862303913051871843324116107542593/438445812715415827585001723282348153241600000000000000000)]
    reserve := (27429/6250000000) }

theorem mixed_004_105_valid : mixed_004_105.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_105]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_105]
  · intro i; fin_cases i <;> norm_num [mixed_004_105]
  · norm_num [mixed_004_105]
  · norm_num [mixed_004_105, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_105, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_105, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_105, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_105]

def mixed_004_106 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(33/5120), (17/2560)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14600579/100000000), (1460183/10000000), (8508471/100000000), (14457059/100000000), (14457059/100000000), (1671539/10000000), (4164903/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(19107/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(699677/12500000), (721/100000000), (2135137/50000000), (4238707/100000000), (1/100000000), (5584233/100000000), (57747/100000000)]
    alternative := .zero
    polynomial := [(-2354219788848671482500486650166994381540711/18589160733341953371586962647558750000000000), (703498704651/18025000000), (-27934054929360681719970537127423376268054478211/9294580366670976685793481323779375000000000), (703498704651/18025000000), (-55865755638932514768458573768196585541727415711/18589160733341953371586962647558750000000000)]
    bernstein := [(816528459473872854684606501543637895240374382296799969/12774373985566570642515670430598144878182400000000000000000), (498409835457215006044825181475597911206157924048963281/6387186992783285321257835215299072439091200000000000000000), (699764879805483555360831801910110302799420995729898307/9580780489174927981886752822948608658636800000000000000000), (78141006380600951305171749024188226755594177445736881/1596796748195821330314458803824768109772800000000000000000), (4571458378340847101270108455982028749746823799492769/798398374097910665157229401912384054886400000000000000000)]
    reserve := (2862893/500000000000) }

theorem mixed_004_106_valid : mixed_004_106.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_106]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_106]
  · intro i; fin_cases i <;> norm_num [mixed_004_106]
  · norm_num [mixed_004_106]
  · norm_num [mixed_004_106, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_106, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_106, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_106, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_106]

def mixed_004_107 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(17/2560), (7/1024)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14604077/100000000), (14605403/100000000), (2127317/25000000), (1807033/12500000), (1807033/12500000), (8356529/50000000), (8327833/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(98411/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5597249/100000000), (721/100000000), (854231/20000000), (1059659/25000000), (1/100000000), (697957/12500000), (59433/100000000)]
    alternative := .zero
    polynomial := [(-20779018702888463749744265952456794914797341/154625670330603589245062320836450000000000000), (1449341049819/36050000000), (-11064848194902958526531936645262837247742168921/3681563579300085458215769543725000000000000), (1449341049819/36050000000), (-464702845167221369650591594835086707610256297341/154625670330603589245062320836450000000000000)]
    bernstein := [(144605152275456728937520461577143003665932764890456513/2213707323973399745825866658248040382464000000000000000000), (211007731703587987622978271743281520907368781903256709/2656448788768079694991039989897648458956800000000000000000), (7190151473014032861428166955742940411654344197036601/96598137773384716181492363269005398507520000000000000000), (171123568735325324227699093465864647613130192753209/3400254449623142009588531187068990027464704000000000000), (25792364157349837021547740090376825816751007513/3626938079598018143561099932873589362629017600000000)]
    reserve := (1777833/250000000000) }

theorem mixed_004_107_valid : mixed_004_107.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_107]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_107]
  · intro i; fin_cases i <;> norm_num [mixed_004_107]
  · norm_num [mixed_004_107]
  · norm_num [mixed_004_107, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_107, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_107, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_107, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_107]

def mixed_004_108 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(7/1024), (9/1280)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(7303787/50000000), (14608979/100000000), (4255033/50000000), (14455467/100000000), (14455467/100000000), (668429/4000000), (8325861/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(12661/6250000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2798541/50000000), (361/50000000), (4272037/100000000), (847713/20000000), (1/100000000), (2791539/50000000), (61119/100000000)]
    alternative := .zero
    polynomial := [(-7895685690853885772966194910831625105427/55542401491690571348789440264800000000000), (372934202059/9025000000), (-83355677508599666962017640885800944636037427/27771200745845285674394720132400000000000), (372934202059/9025000000), (-166703459331508480038262315576691057646969427/55542401491690571348789440264800000000000)]
    bernstein := [(260764192586000478369644260505835784926644069/3908449041581877161076412500008330526405427200000), (49331361713928032943328604989540588190289302047/610695162747168306418189453126301644750848000000000), (3098060683810026058628525682888845657136319590017/40894765362533591947646615164707699425280000000000000), (6160818795908024613877955209192099414935788718979/119276398974056309847302627563730789990400000000000000), (1261809269460990469488878207847189276802457947853/149095498717570387309128284454663487488000000000000000)]
    reserve := (4231547/500000000000) }

theorem mixed_004_108_valid : mixed_004_108.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_108]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_108]
  · intro i; fin_cases i <;> norm_num [mixed_004_108]
  · norm_num [mixed_004_108]
  · norm_num [mixed_004_108, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_108, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_108, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_108, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_108]

def mixed_004_109 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(9/1280), (37/5120)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14611071/100000000), (14612557/100000000), (531929/6250000), (1445467/10000000), (1445467/10000000), (1670839/10000000), (16647779/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(208333/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1399229/25000000), (361/50000000), (106823/2500000), (2119247/50000000), (1/100000000), (2233/40000), (62803/100000000)]
    alternative := .zero
    polynomial := [(-16461633472965252236580299212468876343/109489547781762944151878445000000000000), (3068317230357/72200000000), (-2136274294670730145909732375546196485629959/711682060581459136987209892500000000000), (3068317230357/72200000000), (-4272334588106311743540389207202630875867459/1423364121162918273974419785000000000000)]
    bernstein := [(20019726904513941984335124394844626696838524177/293908766860313243973120236401459200000000000000000), (1255820545683329920751754882900543343101868449193/15283255876736288686602252292875878400000000000000000), (1088255290972142854484365045872859069104256236619/14107620809295035710709771347270041600000000000000000), (12966282627894937398547063562648037440106680051057/244532094027780618985636036686014054400000000000000000), (9610725286283043593527370415366197278705125048301/978128376111122475942544146744056217600000000000000000)]
    reserve := (9825627/1000000000000) }

theorem mixed_004_109_valid : mixed_004_109.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_109]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_109]
  · intro i; fin_cases i <;> norm_num [mixed_004_109]
  · norm_num [mixed_004_109]
  · norm_num [mixed_004_109, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_109, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_109, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_109, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_109]

def mixed_004_110 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(37/5120), (19/2560)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(1826821/12500000), (1827017/12500000), (4255831/50000000), (903367/6250000), (903367/6250000), (8353027/50000000), (16643837/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(53523/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(22387/400000), (361/50000000), (4273803/100000000), (2119211/50000000), (1/100000000), (2790961/50000000), (64487/100000000)]
    alternative := .zero
    polynomial := [(-5504457550902458280037308784715270075024761/34668427648228355141715560097150000000000000), (8297977603/190000000), (-52037342402533737373381853167093054328358524761/17334213824114177570857780048575000000000000), (8297977603/190000000), (-104069180347516572288483669025401393386642024761/34668427648228355141715560097150000000000000)]
    bernstein := [(1656408454656311125402197461166948406360990477782440279/23823962072461276427766684152253093249024000000000000000000), (331821883682252453806224192063645755735662221799360091/3970660345410212737961114025375515541504000000000000000000), (1403059393176716764279889873372677217994498018484797653/17867971554345957320825013114189819936768000000000000000000), (53993758690130021839508004102779005179427119832426379/992665086352553184490278506343878885376000000000000000000), (16640146155457212549016266672640466197658050924670519/1488997629528829776735417759515818328064000000000000000000)]
    reserve := (11175401/1000000000000) }

theorem mixed_004_110_valid : mixed_004_110.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_110]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_110]
  · intro i; fin_cases i <;> norm_num [mixed_004_110]
  · norm_num [mixed_004_110]
  · norm_num [mixed_004_110, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_110, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_110, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_110, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_110]

def mixed_004_111 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(19/2560), (39/5120)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(2923613/20000000), (7309859/50000000), (425623/5000000), (14453073/100000000), (14453073/100000000), (4175929/25000000), (16639897/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(109927/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2798293/50000000), (361/50000000), (4274687/100000000), (4238351/100000000), (1/100000000), (5581343/100000000), (6617/10000000)]
    alternative := .zero
    polynomial := [(-652925139870564100110181185234507075500861569/3899593941550231096477692608616525000000000000), (80955787311/1805000000), (-5853953159617312194327483086209625804679569186569/1949796970775115548238846304308262500000000000), (80955787311/1805000000), (-11707253394094753824554855991234017102283637511569/3899593941550231096477692608616525000000000000)]
    bernstein := [(11880079463910284459194786179267849008225999647392531551/167486284466379781006139105475489026801664000000000000000000), (28460433601485482615253458737348516592903093825819841731/334972568932759562012278210950978053603328000000000000000000), (12353835690815466736370935490231209472845731694877238041/154602724122812105544128405054297563201536000000000000000000), (113033358476420940069549551805685100768231596221176431/2027065470092342281466131382456750702592000000000000000000), (50792859147084551817611218058136132063114206255166611/4054130940184684562932262764913501405184000000000000000000)]
    reserve := (12528667/1000000000000) }

theorem mixed_004_111_valid : mixed_004_111.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_111]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_111]
  · intro i; fin_cases i <;> norm_num [mixed_004_111]
  · norm_num [mixed_004_111]
  · norm_num [mixed_004_111, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_111, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_111, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_111, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_111]

def mixed_004_112 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(39/5120), (1/128)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14621561/100000000), (14623301/100000000), (4256629/50000000), (14452273/100000000), (14452273/100000000), (16701377/100000000), (8317979/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(11281/5000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5596421/100000000), (361/50000000), (4275571/100000000), (4238279/100000000), (1/100000000), (1395191/25000000), (67853/100000000)]
    alternative := .zero
    polynomial := [(-183337708475240212684396803418502501746573595377/1039741118464133473014378470618720100000000000000), (830832873743/18050000000), (-1561032926097830618617253202364509637676937609845377/519870559232066736507189235309360050000000000000), (830832873743/18050000000), (-3121882514487185997021822007925600772852128646095377/1039741118464133473014378470618720100000000000000)]
    bernstein := [(51677214092421142270040309061081185118762918100963429008143/714504656017586402492104651051823954380455936000000000000000000), (1542645994131632728594195852431185938331717187628773875417/17862616400439660062302616276295598859511398400000000000000000), (108926215181457865359000167664316299088656594938747611901/1339696230032974504672696220722169914463354880000000000000000), (6717364900129410274077095605728622352857239880135991/117517213160787237251990896554576308286259200000000000000), (155446369331869820853116545493663994164031705444167/11164135250274787538939135172684749287194624000000000000)]
    reserve := (6961863/500000000000) }

theorem mixed_004_112_valid : mixed_004_112.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_112]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_112]
  · intro i; fin_cases i <;> norm_num [mixed_004_112]
  · norm_num [mixed_004_112]
  · norm_num [mixed_004_112, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_112, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_112, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_112, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_112]

def mixed_004_113 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/128), (41/5120)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14625057/100000000), (14626887/100000000), (1064257/12500000), (903217/6250000), (903217/6250000), (4174759/25000000), (16632021/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(231387/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5596257/100000000), (361/50000000), (855291/20000000), (4238207/100000000), (1/100000000), (697523/12500000), (34767/50000000)]
    alternative := .zero
    polynomial := [(-91489213502278785039432720476650185533668259/493314826614036996323426615750025000000000000), (3408488140593/72200000000), (-740757003728181859996708790810131311206882855759/246657413307018498161713307875012500000000000), (3408488140593/72200000000), (-1481422518242861441208378148899785972228232043259/493314826614036996323426615750025000000000000)]
    bernstein := [(390560470469651875878508989774313135588158922189/5296927617347998284357973883255789715456000000000000), (30989113814897866929248219142126205603631687026019/353128507823199885623864925550385981030400000000000000), (52557017727192649876502987891103558808868155138103167/635631314081759794122956865990694765854720000000000000000), (165320176996136767911425869763682926775392451524371807/2825028062585599084990919404403087848243200000000000000000), (5173553688856739701902001186866856604327815221353249701/339003367510271890198910328528370541789184000000000000000000)]
    reserve := (3815267/250000000000) }

theorem mixed_004_113_valid : mixed_004_113.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_113]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_113]
  · intro i; fin_cases i <;> norm_num [mixed_004_113]
  · norm_num [mixed_004_113]
  · norm_num [mixed_004_113, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_113, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_113, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_113, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_113]

def mixed_004_114 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(41/5120), (21/2560)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(1828569/12500000), (7315237/50000000), (4257427/50000000), (1445067/10000000), (1445067/10000000), (16696693/100000000), (3325617/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(118579/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2798047/50000000), (723/100000000), (213867/5000000), (847627/20000000), (1/100000000), (1394901/25000000), (14243/20000000)]
    alternative := .zero
    polynomial := [(-102941874913316900905412122943871290987923/529118299422960798926149721100000000000000), (1746889081901/36150000000), (-793565556836259983166201793955631866377487923/264559149711480399463074860550000000000000), (1746889081901/36150000000), (-1587028171797606649431498175788319861463987923/529118299422960798926149721100000000000000)]
    bernstein := [(27318082237733114878814697387363942306978046689621197/363607326677880368460455195411843383296000000000000000000), (16201305441180215915211298190978185625109918990820457/181803663338940184230227597705921691648000000000000000000), (3273522191377898921740616367646136779343597494328393/38957927858344325192191628079840362496000000000000000000), (2721104826137698853719984622551287299652032060298577/45450915834735046057556899426480422912000000000000000000), (378154463995279021677126877651306303200313126257437/22725457917367523028778449713240211456000000000000000000)]
    reserve := (133121/8000000000) }

theorem mixed_004_114_valid : mixed_004_114.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_114]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_114]
  · intro i; fin_cases i <;> norm_num [mixed_004_114]
  · norm_num [mixed_004_114]
  · norm_num [mixed_004_114, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_114, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_114, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_114, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_114]

def mixed_004_115 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(21/2560), (43/5120)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14632047/100000000), (914629/6250000), (2128913/25000000), (3612467/25000000), (3612467/25000000), (333887/2000000), (16624151/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(60733/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5595931/100000000), (723/100000000), (171129/4000000), (2119031/50000000), (1/100000000), (348689/6250000), (14579/20000000)]
    alternative := .zero
    polynomial := [(-30758316609544873767060368704350414096927/150671931247139724098593307006000000000000), (1789560478997/36150000000), (-226016724472605792526160785002728121023876927/75335965623569862049296653503000000000000), (1789560478997/36150000000), (-452002690628602040178554509636751891633656927/150671931247139724098593307006000000000000)]
    bernstein := [(495197984970807070096495605704874329480507371749713/6471310171316256085459213331952576757760000000000000000), (3514256558065796973507797369708638905225539155301837/38827861027897536512755279991715460546560000000000000000), (315877651772370425352017531507530459523069622786151/3697891526466432048833836189687186718720000000000000000), (9514242910603485393646044999987386029828618634639693/155311444111590146051021119966861842186240000000000000000), (5598312015051880673563130341282684880899083417599219/310622888223180292102042239933723684372480000000000000000)]
    reserve := (18022857/1000000000000) }

theorem mixed_004_115_valid : mixed_004_115.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_115]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_115]
  · intro i; fin_cases i <;> norm_num [mixed_004_115]
  · norm_num [mixed_004_115]
  · norm_num [mixed_004_115, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_115, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_115, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_115, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_115]

def mixed_004_116 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(43/5120), (11/1280)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14635543/100000000), (2927531/20000000), (8516451/100000000), (2889813/20000000), (2889813/20000000), (4173001/25000000), (8310109/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(62177/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(699471/12500000), (723/100000000), (4279111/100000000), (423799/10000000), (1/100000000), (5578443/100000000), (37287/50000000)]
    alternative := .zero
    polynomial := [(-215341884715375138026974595894720501741817/1006447341026413780663754461050000000000000), (458066841871/9037500000), (-503341112341245542021072255651102613654163939/167741223504402296777292410175000000000000), (458066841871/9037500000), (-3019831332162757876988406559310720961423241817/1006447341026413780663754461050000000000000)]
    bernstein := [(17967897898929871943914979834382770199107146955016061/230541782125579000539442271081805643776000000000000000000), (15893556080223282423947117826103574423320807523154391/172906336594184250404581703311354232832000000000000000000), (3753125088298869076939072198042962759080242876471607/43226584148546062601145425827838558208000000000000000000), (677046256483688497363692774580493349232225664038039/10806646037136515650286356456959639552000000000000000000), (17470096028755722301569645841906501818798140539901/900553836428042970857196371413303296000000000000000000)]
    reserve := (242491/12500000000) }

theorem mixed_004_116_valid : mixed_004_116.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_116]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_116]
  · intro i; fin_cases i <;> norm_num [mixed_004_116]
  · norm_num [mixed_004_116]
  · norm_num [mixed_004_116, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_116, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_116, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_116, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_116]

def mixed_004_117 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(11/1280), (9/1024)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14639037/100000000), (14641249/100000000), (8517249/100000000), (14448261/100000000), (14448261/100000000), (8344829/50000000), (8308143/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(254487/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2797803/50000000), (723/100000000), (4279997/100000000), (2118959/50000000), (1/100000000), (5577861/100000000), (19063/25000000)]
    alternative := .zero
    polynomial := [(-809232465368679834274369845767527104619907707/3612323384205871734494567180694150000000000000), (1250011561273/24100000000), (-5420874569178743726557261973907650330393194907707/1806161692102935867247283590347075000000000000), (1250011561273/24100000000), (-10840939905892118773280249577969533133681769907707/3612323384205871734494567180694150000000000000)]
    bernstein := [(769273298436531594706742471222040412007737843857332213/9696756748587663769265600706722685517824000000000000000000), (723876100978702627426720899206990196814125747388706807/7757405398870131015412480565378148414259200000000000000000), (149303544515276528686537653552949223634909281016978997/1692524814298937676089995759718868744929280000000000000000), (317896532301151840214623818869772274266474142885020319/4964739455276883849863987561842014985125888000000000000000), (82478891007868155130998706472715054438901676430277157/3971791564221507079891190049473611988100710400000000000000)]
    reserve := (2595771/125000000000) }

theorem mixed_004_117_valid : mixed_004_117.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_117]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_117]
  · intro i; fin_cases i <;> norm_num [mixed_004_117]
  · norm_num [mixed_004_117]
  · norm_num [mixed_004_117, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_117, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_117, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_117, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_117]

def mixed_004_118 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(9/1024), (23/2560)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14642531/100000000), (2928969/20000000), (8518047/100000000), (2889491/20000000), (451483/3125000), (16687309/100000000), (4153089/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(260269/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1119089/20000000), (723/100000000), (1070221/25000000), (1059461/25000000), (1/100000000), (17429/312500), (7793/10000000)]
    alternative := .zero
    polynomial := [(-11678757723342160548299992681052902712138419/49842349319909519356333695711600000000000000), (1278540210027/24100000000), (-74812939397016718059581481349091600792224538419/24921174659954759678166847855800000000000000), (1278540210027/24100000000), (-149614200036310093958614662705502148681736938419/49842349319909519356333695711600000000000000)]
    bernstein := [(4424324187592189330374832373453704399536783300809069/54802242632913722192520241547299186645401600000000000000), (12976569110222212642433613362621567679653174414382899/137005606582284305481300603868247966613504000000000000000), (92080744275898340876900213400728437656290577719254151/1027542049367132291109754529011859749601280000000000000000), (56021171602934712747483770843155634994578257013542003/856285041139276909258128774176549791334400000000000000000), (47412809040798758678538114084847112019683859247261421/2140712602848192273145321935441374478336000000000000000000)]
    reserve := (22148143/1000000000000) }

theorem mixed_004_118_valid : mixed_004_118.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_118]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_118]
  · intro i; fin_cases i <;> norm_num [mixed_004_118]
  · norm_num [mixed_004_118]
  · norm_num [mixed_004_118, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_118, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_118, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_118, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_118]

def mixed_004_119 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(23/2560), (47/5120)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(585841/4000000), (7324221/50000000), (4259423/50000000), (288933/2000000), (288933/2000000), (16684959/100000000), (16608427/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(266053/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1398821/25000000), (723/100000000), (4281771/100000000), (1059443/25000000), (1/100000000), (5576697/100000000), (39803/50000000)]
    alternative := .zero
    polynomial := [(-191470017485548131328566908427196925288111/782011792526561566122863532900000000000000), (326773143739/6025000000), (-62225439627715957777421183835619099863002019883/20723312501953881502255883621850000000000000), (326773143739/6025000000), (-124440731344505181503881953625091558288963769883/41446625003907763004511767243700000000000000)]
    bernstein := [(8601332877574039551510906298813043830174969500965941/104712881718446890767586318093444448256000000000000000000), (6709959877328696714959644859982572621926109348713983/69808587812297927178390878728962965504000000000000000000), (1944023944524120688803333447863815924021285557647872511/21361427870563165716587608891062667444224000000000000000000), (317110763999087180175768771063007973455373227575816031/4746983971236259048130579753569481654272000000000000000000), (12633181744239429246976892772341904581942140839836209/537394411838067062052518462668243206144000000000000000000)]
    reserve := (23508211/1000000000000) }

theorem mixed_004_119_valid : mixed_004_119.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_119]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_119]
  · intro i; fin_cases i <;> norm_num [mixed_004_119]
  · norm_num [mixed_004_119]
  · norm_num [mixed_004_119, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_119, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_119, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_119, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_119]

def mixed_004_120 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(47/5120), (3/320)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14649519/100000000), (7326021/50000000), (1703929/20000000), (14445843/100000000), (3611461/25000000), (1042663/6250000), (33209/200000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(271841/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1398781/25000000), (181/25000000), (4282659/100000000), (4237699/100000000), (1/100000000), (1115223/20000000), (40641/50000000)]
    alternative := .zero
    polynomial := [(-6420174477837995455453697258614625362219223/25151718714015734855244409851225000000000000), (2003534532661/36200000000), (-867533330590799437356874075095104652426595604629/289244765211180950835310713289087500000000000), (2003534532661/36200000000), (-1734918997168608600818272715153261168469860167129/578489530422361901670621426578175000000000000)]
    bernstein := [(33211892507507887429300044155640455603619188404164677351/397534978278790629560269886584020289978368000000000000000000), (127485711403611891172479176067039674393369349692464921/1307680849601284965658782521657961480192000000000000000000), (13880601558419942134455898407776151116850218910620963/150277839571115409359981055916338315264000000000000000000), (348238809568987972197466356614915603894593078765121/5108128318755019397104619225226412032000000000000000000), (151110402720818074080268868166820840588094251249751/6065902378521585534061735329956364288000000000000000000)]
    reserve := (12455723/500000000000) }

theorem mixed_004_120_valid : mixed_004_120.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_120]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_120]
  · intro i; fin_cases i <;> norm_num [mixed_004_120]
  · norm_num [mixed_004_120]
  · norm_num [mixed_004_120, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_120, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_120, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_120, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_120]

def mixed_004_121 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/320), (49/5120)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14653013/100000000), (14655643/100000000), (8520443/100000000), (3611259/25000000), (3611259/25000000), (3336051/20000000), (16600573/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(277631/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1398741/25000000), (181/25000000), (4283547/100000000), (2118813/50000000), (1/100000000), (1393883/25000000), (41479/50000000)]
    alternative := .zero
    polynomial := [(-78602731704682358796229290435396488995692833/295225679309291458505677721779260000000000000), (4092898451437/72400000000), (-442847667325070812836266279130095713115064867833/147612839654645729252838860889630000000000000), (4092898451437/72400000000), (-885616731918436943313736328969756029741134042833/295225679309291458505677721779260000000000000)]
    bernstein := [(262990161812553784977887835001064166427783626664927/3095665619074196003940495227924093337600000000000000000), (4898571053367649281152193613653465024550015917184741/49530649905187136063047923646785493401600000000000000000), (222938897122931101987270922628886809508767760557815509/2377471195448982531026300335045703683276800000000000000000), (882126166084430149990692105001853920339556106548579549/12679846375727906832140268453577086310809600000000000000000), (5334223310674114433571322031860905214702700702415648367/202877542011646509314244295257233380972953600000000000000000)]
    reserve := (26292823/1000000000000) }

theorem mixed_004_121_valid : mixed_004_121.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_121]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_121]
  · intro i; fin_cases i <;> norm_num [mixed_004_121]
  · norm_num [mixed_004_121]
  · norm_num [mixed_004_121, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_121, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_121, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_121, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_121]

def mixed_004_122 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(49/5120), (5/512)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(7328253/50000000), (7329623/50000000), (4260621/50000000), (3611057/25000000), (3611057/25000000), (16677901/100000000), (16596649/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(8857/3125000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1118961/20000000), (181/25000000), (1071109/25000000), (264847/6250000), (1/100000000), (5574949/100000000), (10579/12500000)]
    alternative := .zero
    polynomial := [(-94021479365779445528758165555598394179236553/338850216288003808982925189015300000000000000), (522351760757/9050000000), (-508419050345288290654263966631103841296011674053/169425108144001904491462594507650000000000000), (522351760757/9050000000), (-1016744079211210801862999175096652084197844111553/338850216288003808982925189015300000000000000)]
    bernstein := [(1546962396797886371650819110897651576946618698177829819/17912007350147727713293473344434854690816000000000000000000), (1088968119171096326442166300777683769427652668105291/10855762030392562250480892936021124055040000000000000000), (664907995306600455342407765495895507525661938110251093/6985682866557613808184454604329593329418240000000000000000), (100158711721371826283656074144620429424862352056727/1411249063951033092562516081682746127155200000000000000), (644610312454877704479787413832700373521123638466767/23285609555192046027281515347765311098060800000000000000)]
    reserve := (1107311/40000000000) }

theorem mixed_004_122_valid : mixed_004_122.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_122]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_122]
  · intro i; fin_cases i <;> norm_num [mixed_004_122]
  · norm_num [mixed_004_122]
  · norm_num [mixed_004_122, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_122, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_122, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_122, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_122]

def mixed_004_123 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(5/512), (51/5120)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14659999/100000000), (3665713/25000000), (8522041/100000000), (14443419/100000000), (14443419/100000000), (3335109/20000000), (8296363/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(14461/5000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5594647/100000000), (181/25000000), (171413/4000000), (4237479/100000000), (1/100000000), (1114873/20000000), (17261/20000000)]
    alternative := .zero
    polynomial := [(-472801876629629056237214882195966305442641/1636356108576434772395779754580000000000000), (33318877521/565625000), (-2455894423372944128073719755867127872226342641/818178054288217386197889877290000000000000), (33318877521/565625000), (-4911316044869258627091202296852059778147242641/1636356108576434772395779754580000000000000)]
    bernstein := [(9869636596889689847126971337765957143224271334399/112449535535129799419473241829440099450880000000000000), (22877245502615034084798357895819291932411213760469/224899071070259598838946483658880198901760000000000000), (3258486479377092697381168325899719185730121783340621/33734860660538939825841972548832029835264000000000000000), (22297591556969750877573151625663910527003437095037/308080919274328217587597922820383834112000000000000000), (447891507238733721805111863044838724823939844350183/15404045963716410879379896141019191705600000000000000000)]
    reserve := (1163049/40000000000) }

theorem mixed_004_123_valid : mixed_004_123.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_123]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_123]
  · intro i; fin_cases i <;> norm_num [mixed_004_123]
  · norm_num [mixed_004_123]
  · norm_num [mixed_004_123, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_123, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_123, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_123, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_123]

def mixed_004_124 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(51/5120), (13/1280)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(3665873/25000000), (14666459/100000000), (213071/2500000), (14442609/100000000), (14442609/100000000), (4168297/25000000), (4147201/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(147509/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(699311/12500000), (181/25000000), (2143107/50000000), (847481/20000000), (1/100000000), (5573781/100000000), (43989/50000000)]
    alternative := .zero
    polynomial := [(-3922596032500022742573110970767933347209457/13047671169918023234503800173118750000000000), (2175444994727/36200000000), (-19587831864887744340684189148926781498749365707/6523835584959011617251900086559375000000000), (2175444994727/36200000000), (-39171741133742988658625805186882795064151521957/13047671169918023234503800173118750000000000)]
    bernstein := [(799712423578992390563509308700706556576778603262140043/8966291354201595006905913685002267131904000000000000000000), (231199345631103983004144733553432903074638324953600309/2241572838550398751726478421250566782976000000000000000000), (164760326545630966365341627607867625868930433394036001/1681179628912799063794858815937925087232000000000000000000), (10335695416055477991016515744267966067249722120560821/140098302409399921982904901328160423936000000000000000000), (1066736892175553303785600455504882777909353617571723/35024575602349980495726225332040105984000000000000000000)]
    reserve := (30456811/1000000000000) }

theorem mixed_004_124_valid : mixed_004_124.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_124]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_124]
  · intro i; fin_cases i <;> norm_num [mixed_004_124]
  · norm_num [mixed_004_124]
  · norm_num [mixed_004_124, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_124, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_124, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_124, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_124]

def mixed_004_125 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(13/1280), (53/5120)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(1833373/12500000), (14670069/100000000), (8523639/100000000), (7220899/50000000), (7220899/50000000), (4167707/25000000), (4146221/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(300819/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5594331/100000000), (29/4000000), (857421/20000000), (4237331/100000000), (1/100000000), (1393299/25000000), (1793/2000000)]
    alternative := .zero
    polynomial := [(-425586046673598521303774829163800634668163/1363432124768054880294555255225000000000000), (4437083568311/72500000000), (-2044648451913260077595277586820172961018188163/681716062384027440147277627612500000000000), (4437083568311/72500000000), (-4088871317779846556669251398811182121401708163/1363432124768054880294555255225000000000000)]
    bernstein := [(11434137390832585534688037948708938275561908754033/126204663495573002077549777328799744000000000000000000), (72858365065055363058619539103739733325201727412577/697130522166022297190274960482893824000000000000000000), (17454354416071893184062944662949543675488519855627031/175676891585837618891949290041689243648000000000000000000), (837996105844169152129539857981425484943510171195697/11154088354656356755044399367726301184000000000000000000), (29826880760665452239279254888611815112717536720053997/936943421791133967423729546889009299456000000000000000000)]
    reserve := (15917119/500000000000) }

theorem mixed_004_125_valid : mixed_004_125.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_125]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_125]
  · intro i; fin_cases i <;> norm_num [mixed_004_125]
  · norm_num [mixed_004_125]
  · norm_num [mixed_004_125, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_125, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_125, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_125, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_125]

def mixed_004_126 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(53/5120), (27/2560)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(3667619/25000000), (183421/1250000), (4262219/50000000), (7220493/50000000), (7220493/50000000), (4167117/25000000), (4145241/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(4791/1562500), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2797087/50000000), (29/4000000), (857599/20000000), (4237257/100000000), (1/100000000), (5572611/100000000), (45661/50000000)]
    alternative := .zero
    polynomial := [(-70602083188100494351608165413975165709871/217702167155446994074779376575000000000000), (113083621353/1812500000), (-326569846258900811325276204777119237281509871/108851083577723497037389688287500000000000), (113083621353/1812500000), (-653069090434613522156200801388824499397309871/217702167155446994074779376575000000000000)]
    bernstein := [(13764755453451892803247805967887389939659251497598849/149603790112155230050029312128782958592000000000000000000), (7923974733136239579905064242121025108468742087893391/74801895056077615025014656064391479296000000000000000000), (11308155781828211520804728356921131452429420931324707/112202842584116422537521984096587218944000000000000000000), (1431689119384363102952794758053932274599179253764271/18700473764019403756253664016097869824000000000000000000), (310990457765178783089424450952299419187784654881089/9350236882009701878126832008048934912000000000000000000)]
    reserve := (4157521/125000000000) }

theorem mixed_004_126_valid : mixed_004_126.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_126]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_126]
  · intro i; fin_cases i <;> norm_num [mixed_004_126]
  · norm_num [mixed_004_126]
  · norm_num [mixed_004_126, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_126, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_126, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_126, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_126]

def mixed_004_127 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(27/2560), (11/1024)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(917123/6250000), (7338647/50000000), (8525237/100000000), (7220087/50000000), (7220087/50000000), (8333053/50000000), (16577047/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(31243/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5594017/100000000), (29/4000000), (2144443/50000000), (4237183/100000000), (1/100000000), (222881/4000000), (1453/1562500)]
    alternative := .zero
    polynomial := [(-192877080551953997746509998802225486489111707/572840105351083260268797316297200000000000000), (460966368257/7250000000), (-859563980820294288622618120294755109113194294207/286420052675541630134398658148600000000000000), (460966368257/7250000000), (-1718935084560036623247489730590707992739899476707/572840105351083260268797316297200000000000000)]
    bernstein := [(2298694949950930447134520433564996163336738413385633613/24603295183200972010275406427490418163712000000000000000000), (1056467710060404184838044376538245895605312287627674589/9841318073280388804110162570996167265484800000000000000000), (1206820065156715946930927260400720346492724769561372743/11809581687936466564932195085195400718581760000000000000000), (9441524401660228352514662348216318492241567074500529/121123914748066323742894308566106674036736000000000000000), (1677725154677474099249637970247107100719947904318849/48449565899226529497157723426442669614694400000000000000)]
    reserve := (865707/25000000000) }

theorem mixed_004_127_valid : mixed_004_127.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_127]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_127]
  · intro i; fin_cases i <;> norm_num [mixed_004_127]
  · norm_num [mixed_004_127]
  · norm_num [mixed_004_127, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_127, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_127, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_127, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_127]

def mixed_004_128 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(11/1024), (7/640)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14677459/100000000), (14680909/100000000), (8526037/100000000), (14439361/100000000), (14439361/100000000), (16663743/100000000), (1657313/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1989/625000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5593861/100000000), (29/4000000), (4289777/100000000), (4237109/100000000), (1/100000000), (5571439/100000000), (47331/50000000)]
    alternative := .zero
    polynomial := [(-27163002940521294091804565566147565859408321679/77754777221916334398869706853275300000000000000), (234804175933/3625000000), (-116709510927944271095635408770962292446551222161679/38877388610958167199434853426637650000000000000), (234804175933/3625000000), (-8047995132860276582661345275046842666456656413851/2681199214548839117202403684595700000000000000)]
    bernstein := [(623728956723132684682948141756801938563015546559726053/6576329359279190462844951833598512915388825600000000000000), (149025401720568919765606672721233675276659440517484771/1370068616516498013092698298666356857372672000000000000000), (51136361595881781582515237850822176135476541559294337/493528411737777917277850064482647020666880000000000000000), (552201774546927257818540860508901627903256064361200591/6957379693247841472736358547915093416345600000000000000000), (470122725351132717680991973266307863173437250474925521/13045086924839702761380672277340800155648000000000000000000)]
    reserve := (36038297/1000000000000) }

theorem mixed_004_128_valid : mixed_004_128.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_128]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_128]
  · intro i; fin_cases i <;> norm_num [mixed_004_128]
  · norm_num [mixed_004_128]
  · norm_num [mixed_004_128, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_128, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_128, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_128, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_128]

def mixed_004_129 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(7/640), (57/5120)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14680951/100000000), (14684527/100000000), (2131709/25000000), (7219273/50000000), (14438547/100000000), (8330689/50000000), (129447/781250)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(324053/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2796853/50000000), (29/4000000), (4290669/100000000), (2118517/50000000), (1/100000000), (5570853/100000000), (96331/100000000)]
    alternative := .zero
    polynomial := [(-2388547586264033199666000294516957055510266409/6594184917079576859240014159759050000000000000), (164916910039/2500000000), (-9900966404182616660685378248695337922289067796409/3297092458539788429620007079879525000000000000), (164916910039/2500000000), (-19799544260778969288171090497096158887522625326409/6594184917079576859240014159759050000000000000)]
    bernstein := [(106500724420962662667926467439775201639410758397064791/1106320646977861501560713134013360898048000000000000000000), (975360841116757748378307384885731221118763289859275241/8850565175822892012485705072106887184384000000000000000000), (22313758092730823857474811224719557209216099590406263173/212413564219749408299656921730565292425216000000000000000000), (45769085153678609039124901997408676805635397741777947241/566436171252665088799085124614840779800576000000000000000000), (169761704627482577107198452594542152840713843879685608791/4531489370021320710392680996918726238404608000000000000000000)]
    reserve := (37462673/1000000000000) }

theorem mixed_004_129_valid : mixed_004_129.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_129]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_129]
  · intro i; fin_cases i <;> norm_num [mixed_004_129]
  · norm_num [mixed_004_129]
  · norm_num [mixed_004_129, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_129, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_129, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_129, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_129]

def mixed_004_130 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(57/5120), (29/2560)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14684441/100000000), (7344073/50000000), (1705527/20000000), (14437731/100000000), (3609433/25000000), (4164753/25000000), (8282651/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(82467/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(111871/2000000), (29/4000000), (2145781/50000000), (26481/625000), (1/100000000), (2785133/50000000), (97999/100000000)]
    alternative := .zero
    polynomial := [(-4402164989451882694346360112306025725649/11728584088829869950046057700000000000000), (1217292258157/18125000000), (-17615784108055890049245624957669636298085649/5864292044414934975023028850000000000000), (1217292258157/18125000000), (-35227166051122328215796903555226966570445649/11728584088829869950046057700000000000000)]
    bernstein := [(787333254444025968057766884828083413996119219561551/8059821614385640054940955442436636672000000000000000000), (449844235923443716762308499346178384983406925393547/4029910807192820027470477721218318336000000000000000000), (214528776870842722877500909115920438607737228395959/2014955403596410013735238860609159168000000000000000000), (82826520208086438224083479413295503892136346168723/1007477701798205006867619430304579584000000000000000000), (19573662467181149314313901036737856787927450564831/503738850899102503433809715152289792000000000000000000)]
    reserve := (7771353/200000000000) }

theorem mixed_004_130_valid : mixed_004_130.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_130]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_130]
  · intro i; fin_cases i <;> norm_num [mixed_004_130]
  · norm_num [mixed_004_130]
  · norm_num [mixed_004_130, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_130, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_130, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_130, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_130]

def mixed_004_131 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(29/2560), (59/5120)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(3671983/25000000), (1836471/12500000), (1705687/20000000), (3609229/25000000), (3609229/25000000), (4164161/25000000), (1656139/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(167843/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1398349/25000000), (29/4000000), (858491/20000000), (847377/20000000), (1/100000000), (5569679/100000000), (49833/50000000)]
    alternative := .zero
    polynomial := [(-8840509095092387114710133922679495126961741/22744201316665235147295665649525000000000000), (1238958712087/18125000000), (-3796882400353956158905483445494115122556975749/1263566739814735285960870313862500000000000), (1238958712087/18125000000), (-68335042697276118473183991884971392710898601741/22744201316665235147295665649525000000000000)]
    bernstein := [(32270354517014466335194101825148454621447033011420193/325618669429057749125948756024201576448000000000000000000), (220866202882575134479685421921924223348726936072349509/1953712016574346494755692536145209458688000000000000000000), (7395983384370995668684102550739879692853463680504427/68551298827170052447568159162989805568000000000000000000), (653519404570756967034464631727894760551672938219754069/7814848066297385979022770144580837834752000000000000000000), (209730457945733627833454301707153368316085616565463233/5209898710864923986015180096387225223168000000000000000000)]
    reserve := (10064037/250000000000) }

theorem mixed_004_131_valid : mixed_004_131.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_131]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_131]
  · intro i; fin_cases i <;> norm_num [mixed_004_131]
  · norm_num [mixed_004_131]
  · norm_num [mixed_004_131, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_131, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_131, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_131, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_131]

def mixed_004_132 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(59/5120), (3/256)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14691423/100000000), (14695391/100000000), (1705847/20000000), (14436099/100000000), (14436099/100000000), (8327137/50000000), (16557479/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(341507/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2796621/50000000), (363/50000000), (1073337/25000000), (423681/10000000), (1/100000000), (5569091/100000000), (25333/25000000)]
    alternative := .zero
    polynomial := [(-133483192584870658701171962244655508436491/332265983184012934454354529650000000000000), (1008524070749/14520000000), (-498696886034153858365376748961783207334186491/166132991592006467227177264825000000000000), (1008524070749/14520000000), (-997260288875722846072052325961321759159936491/332265983184012934454354529650000000000000)]
    bernstein := [(68867553593537161146322240374629613403272683187184847/684994335047338321690773268625381916672000000000000000000), (559982089030481280885808851382870228165071136469777/4892816678909559440648380490181299404800000000000000000), (187136086443052488233654326369236744472942797644767/1712485837618345804226933171563454791680000000000000000), (207993900136962634987094418822513114226010639053/2446408339454779720324190245090649702400000000000000), (2379081163485305745611461998222269806939256429/57082861253944860140897772385448493056000000000000)]
    reserve := (20838839/500000000000) }

theorem mixed_004_132_valid : mixed_004_132.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_132]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_132]
  · intro i; fin_cases i <;> norm_num [mixed_004_132]
  · norm_num [mixed_004_132]
  · norm_num [mixed_004_132, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_132, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_132, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_132, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_132]

def mixed_004_133 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/256), (61/5120)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14694913/100000000), (14699017/100000000), (4265017/50000000), (7217641/50000000), (7217641/50000000), (16651903/100000000), (1655357/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(347331/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5593089/100000000), (363/50000000), (2147121/50000000), (847347/20000000), (1/100000000), (696063/12500000), (51499/50000000)]
    alternative := .zero
    polynomial := [(-67930856642848808746323110460849991476663929/163470163521936758624740559949300000000000000), (1709820019089/24200000000), (-245434995630208916655076460271596436121526913929/81735081760968379312370279974650000000000000), (1709820019089/24200000000), (-10016368579668877234722583621076163719419942121/3336125786161974665811031835700000000000000)]
    bernstein := [(2863357526259904074414806769382281931888576373551/28083960247939622274940265658678836723712000000000000), (325433903858861522600215580042287510840197820319317/2808396024793962227494026565867883672371200000000000000), (13324977477030819083328177084919945187599162326054739/120359829634026952606886852822909300244480000000000000000), (69366313666079053404364806561747538768620569384924239/802398864226846350712579018819395334963200000000000000000), (4841255803207849954406781226857205234017533334960591511/112335840991758489099761062634715346894848000000000000000000)]
    reserve := (4309627/100000000000) }

theorem mixed_004_133_valid : mixed_004_133.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_133]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_133]
  · intro i; fin_cases i <;> norm_num [mixed_004_133]
  · norm_num [mixed_004_133]
  · norm_num [mixed_004_133, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_133, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_133, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_133, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_133]

def mixed_004_134 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(61/5120), (31/2560)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(7349201/50000000), (7351323/50000000), (2132709/25000000), (2886893/20000000), (14434463/100000000), (2081191/12500000), (827483/5000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(353157/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1118587/20000000), (363/50000000), (134223/3125000), (4236661/100000000), (1/100000000), (1113583/20000000), (104663/100000000)]
    alternative := .zero
    polynomial := [(-25424768699232495868813326464240615671009/59180640758904772991315696550000000000000), (869395409957/12100000000), (-88884719105425406199740192424699685381171009/29590320379452386495657848275000000000000), (869395409957/12100000000), (-177744013442151579903611571522935130146671009/59180640758904772991315696550000000000000)]
    bernstein := [(4203089533417936614178392232167246161541283614953231/40668626658531299324160801390993604608000000000000000000), (794891928166593863197280204339350483578207920758967/6778104443088549887360133565165600768000000000000000000), (3419197284517185201374657915862838358251262548915013/30501469993898474493120601043245203456000000000000000000), (11448136425940730922141975671647997033129607596219/130348162367087497833848722407030784000000000000000000), (668643693887889511923326582721740884887657627719/15040172580817788211597929508503552000000000000000000)]
    reserve := (22228591/500000000000) }

theorem mixed_004_134_valid : mixed_004_134.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_134]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_134]
  · intro i; fin_cases i <;> norm_num [mixed_004_134]
  · norm_num [mixed_004_134]
  · norm_num [mixed_004_134, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_134, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_134, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_134, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_134]

def mixed_004_135 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(31/2560), (63/5120)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(3675473/25000000), (7353137/50000000), (4265817/50000000), (3608411/25000000), (3608411/25000000), (16647157/100000000), (3309151/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(179493/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5592783/100000000), (363/50000000), (429603/10000000), (847317/20000000), (1/100000000), (2783663/50000000), (106327/100000000)]
    alternative := .zero
    polynomial := [(-359617732043139975399271362109426078373577389/810110521411277161038332586917700000000000000), (20088526191/275000000), (-1217147590028379761612750423090139308044824077389/405055260705638580519166293458850000000000000), (20088526191/275000000), (-811311854108238794416700524939389730003758192463/270036840470425720346110862305900000000000000)]
    bernstein := [(280551920716420714437766667346973378548368125712601887/2676460150466879363270279894755845341184000000000000000000), (2754513889019217158764837393008297280072722522826530321/23195987970712954481675759087883992956928000000000000000000), (6774247061372842132133417677950679936168918759189433471/59646826210404740095737666225987410460672000000000000000000), (24854321030898433511721992751576732482624113250215674227/278351855648555453780109109054607915483136000000000000000000), (25555264213202085007957091717900284766285057518968260371/556703711297110907560218218109215830966272000000000000000000)]
    reserve := (9180921/200000000000) }

theorem mixed_004_135_valid : mixed_004_135.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_135]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_135]
  · intro i; fin_cases i <;> norm_num [mixed_004_135]
  · norm_num [mixed_004_135]
  · norm_num [mixed_004_135, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_135, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_135, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_135, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_135]

def mixed_004_136 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(63/5120), (1/80)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14705381/100000000), (7354953/50000000), (4266217/50000000), (1804103/12500000), (1804103/12500000), (16644781/100000000), (330837/2000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(182409/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5592631/100000000), (363/50000000), (2148463/50000000), (4236509/100000000), (1/100000000), (5566737/100000000), (107991/100000000)]
    alternative := .zero
    polynomial := [(-24612755858637006270794502867881664199480847/53686561405968137344514409578700000000000000), (449204771109/6050000000), (-80689703837942789470982443395275224315202980847/26843280702984068672257204789350000000000000), (449204771109/6050000000), (-161354794920026941935694092287682566966206480847/53686561405968137344514409578700000000000000)]
    bernstein := [(3919900247135274326325718096429803360637138446348643633/36893124075732628658036107862602502111232000000000000000000), (69280744813722030430723851656013627605812950629838991/576455063683322322781814185353164095488000000000000000000), (3107636842335893631228249974549602862148809452580371/27021331110155733880397539938429566976000000000000000000), (12767306083829469343968875625275261018547359585039/140736099532061113960403853845987328000000000000000000), (104051828120034907085438366410367397655825557553/2199001555188454905631310216343552000000000000000000)]
    reserve := (36967/781250000) }

theorem mixed_004_136_valid : mixed_004_136.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_136]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_136]
  · intro i; fin_cases i <;> norm_num [mixed_004_136]
  · norm_num [mixed_004_136]
  · norm_num [mixed_004_136, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_136, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_136, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_136, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_136]

def mixed_004_137 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/80), (13/1024)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(1470887/10000000), (14713539/100000000), (4266617/50000000), (14432003/100000000), (14432003/100000000), (3328481/20000000), (8268973/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(370653/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(34953/625000), (727/100000000), (4297821/100000000), (4236433/100000000), (1/100000000), (5566147/100000000), (109653/100000000)]
    alternative := .zero
    polynomial := [(-296558290765948040958250605824158766790966257/627523811394972745422576457346340000000000000), (5477663544451/72700000000), (-942205124039589643130138589350251062462050966257/313761905697486372711288228673170000000000000), (5477663544451/72700000000), (-628037896596137779406439642698225988719103655419/209174603798324248474192152448780000000000000)]
    bernstein := [(2767980913150106195953409782083022626164770224143/25703375314738083652508731692906086400000000000000000), (40004289701848924781639434322359270226296170266819/329003204028647470752111765669197905920000000000000000), (1470607816424356131084084266473563132878503807403189/12633723034700062876881091801697199587328000000000000000), (993148155216477690614389315791498342286796479140031/10780776989610720321605198337448276981186560000000000000), (1345401528003054320037220486593679821419645073702743/27598789093403444023309307743867589071837593600000000000)]
    reserve := (4874857/100000000000) }

theorem mixed_004_137_valid : mixed_004_137.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_137]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_137]
  · intro i; fin_cases i <;> norm_num [mixed_004_137]
  · norm_num [mixed_004_137]
  · norm_num [mixed_004_137, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_137, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_137, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_137, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_137]

def mixed_004_138 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(13/1024), (33/2560)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(7356179/50000000), (588687/4000000), (4267017/50000000), (14431181/100000000), (14431181/100000000), (8320013/50000000), (4133511/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(376491/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5592329/100000000), (727/100000000), (4298717/100000000), (2118179/50000000), (1/100000000), (5565557/100000000), (22263/20000000)]
    alternative := .zero
    polynomial := [(-111826696317994180737983895995923168629444305827/229345890500148703372285873255078950000000000000), (5564924432901/72700000000), (-8401940971409675819143817554703588799065848887947/2796901103660350041125437478720475000000000000), (5564924432901/72700000000), (-688847332959275422989055055589698358354770164505827/229345890500148703372285873255078950000000000000)]
    bernstein := [(1100623498348651661841276056483896529907371870881293173/10086738935502190224596712841148059198955716608000000000000), (15512093594403712991871851685894089559301524813681246413/126084236693777377807458910514350739986946457600000000000000), (557186825940218325812992590514847481360364967003767079471/4728158876016651667779709144288152749510492160000000000000000), (368638786820112826118718950017113416066639454167120671193/3940132396680543056483090953573460624592076800000000000000000), (494254114040496050013150684851447451599743718568859576733/9850330991701357641207727383933651561480192000000000000000000)]
    reserve := (12544099/250000000000) }

theorem mixed_004_138_valid : mixed_004_138.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_138]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_138]
  · intro i; fin_cases i <;> norm_num [mixed_004_138]
  · norm_num [mixed_004_138]
  · norm_num [mixed_004_138, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_138, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_138, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_138, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_138]

def mixed_004_139 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(33/2560), (67/5120)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14715847/100000000), (14720813/100000000), (4267417/50000000), (14430359/100000000), (14430359/100000000), (8318823/50000000), (16530143/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(95583/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5592179/100000000), (727/100000000), (2149807/50000000), (2118141/50000000), (1/100000000), (5564967/100000000), (7061/6250000)]
    alternative := .zero
    polynomial := [(-12192830654922239003934774057646576846439002589/24248080473473155191860546096175900000000000000), (2826136351919/36350000000), (-36434177421319279426552335265589598936877013190089/12124040236736577595930273048087950000000000000), (2826136351919/36350000000), (-72856162011983636614100735757121551296907587377589/24248080473473155191860546096175900000000000000)]
    bernstein := [(115134781098477535874933200989603275646869054379893904331/1041447126243433970829736508757759611633664000000000000000000), (13646122493041185757737229893570410014863103352418919451/109626013288782523245235421974501011750912000000000000000000), (1490924406293007362556260183939169272668969218027376929193/12497365514921207649956838105093115339603968000000000000000000), (41663680803109105494493387078541529895560790865970947251/438504053155130092980941687898004047003648000000000000000000), (860170137065763489434581309781379484338797138693381727931/16663154019894943533275784140124153786138624000000000000000000)]
    reserve := (51621087/1000000000000) }

theorem mixed_004_139_valid : mixed_004_139.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_139]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_139]
  · intro i; fin_cases i <;> norm_num [mixed_004_139]
  · norm_num [mixed_004_139]
  · norm_num [mixed_004_139, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_139, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_139, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_139, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_139]

def mixed_004_140 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(67/5120), (17/1280)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(2943867/20000000), (3681113/25000000), (4267817/50000000), (2885907/20000000), (2885907/20000000), (3327053/20000000), (16526243/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(15527/4000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5592029/100000000), (727/100000000), (4300511/100000000), (847241/20000000), (1/100000000), (695547/12500000), (28659/25000000)]
    alternative := .zero
    polynomial := [(-1020301988495676918758257819887500897495034959/1968462329141384829962178129174060000000000000), (2869846656211/36350000000), (-2958826149377756085174077086935074155708763409959/984231164570692414981089064587030000000000000), (2869846656211/36350000000), (-5916631996767016493429395916050260810520031784959/1968462329141384829962178129174060000000000000)]
    bernstein := [(151505906158949581362178895303584053255868908732759182161/1352717012331237696774092157076648190646681600000000000000000), (14195885373513924435184547464371965378879077708856542937/112726417694269808064507679756387349220556800000000000000000), (30626404071173710935843833588860640325131409589388268283/253634439812107068145142279451871535746252800000000000000000), (679564064389553526228071926433095398965355610046116337/7045401105891863004031729984774209326284800000000000000000), (1203005247899429200573689884219942745460937708344217/22678329739995267180359645873736725299200000000000000000)]
    reserve := (26523233/500000000000) }

theorem mixed_004_140_valid : mixed_004_140.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_140]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_140]
  · intro i; fin_cases i <;> norm_num [mixed_004_140]
  · norm_num [mixed_004_140]
  · norm_num [mixed_004_140, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_140, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_140, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_140, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_140]

def mixed_004_141 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(17/1280), (69/5120)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(7361411/50000000), (7364047/50000000), (4268217/50000000), (14428711/100000000), (14428711/100000000), (8316441/50000000), (3304469/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(394021/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(139797/2500000), (727/100000000), (134419/3125000), (4236129/100000000), (1/100000000), (1112757/20000000), (14537/12500000)]
    alternative := .zero
    polynomial := [(-308608750694413832013036914080396196889881/577859437513542066487053877050000000000000), (1456800453901/18175000000), (-868914205603530486276360240559152763175702381/288929718756771033243526938525000000000000), (1456800453901/18175000000), (-1737519802456366558720707444204225130154514881/577859437513542066487053877050000000000000)]
    bernstein := [(175961321554812061175622718970344143919775359692799/1551179616128511707926346255824846848000000000000000000), (790328819529053812120428641299206307068536069644043/6204718464514046831705385023299387392000000000000000000), (9098124582705820070964938283172968671807495900770453/74456621574168561980464620279592648704000000000000000000), (9718224856793841787862300199405982717965787773753907/99275495432224749307286160372790198272000000000000000000), (21629688806001312120422535524441995551470347148411599/397101981728898997229144641491160793088000000000000000000)]
    reserve := (54468851/1000000000000) }

theorem mixed_004_141_valid : mixed_004_141.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_141]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_141]
  · intro i; fin_cases i <;> norm_num [mixed_004_141]
  · norm_num [mixed_004_141]
  · norm_num [mixed_004_141, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_141, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_141, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_141, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_141]

def mixed_004_142 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(69/5120), (7/512)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(1472631/10000000), (7365869/50000000), (1707447/20000000), (7213943/50000000), (7213943/50000000), (8315249/50000000), (1032403/6250000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(39987/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5591731/100000000), (727/100000000), (4302307/100000000), (4236053/100000000), (1/100000000), (5563193/100000000), (58977/50000000)]
    alternative := .zero
    polynomial := [(-74278560634083414044218505487159653788153206867/135044768004879538771289658425414150000000000000), (1478699474363/18175000000), (-1828264129391929266681792460057597498037141241861803/607701456021957924470803462914363675000000000000), (1478699474363/18175000000), (-3655859751738151782637186953565810559190189104861803/1215402912043915848941606925828727350000000000000)]
    bernstein := [(10661522446098503331540926791802865163717026196314792694493/92802057932298365990760497068826340720902144000000000000000000), (3586753099163955850070854785482876570267145633342645911597/27840617379689509797228149120647902216270643200000000000000000), (3098277885450699737798238860226792494908143633287191916407/25056555641720558817505334208583111994643578880000000000000000), (82973585952323460893221738052881204856754481897920038383/835218521390685293916844473619437066488119296000000000000000), (4669543294808231629972163066069876883818288197833704053/83521852139068529391684447361943706648811929600000000000000)]
    reserve := (27954021/500000000000) }

theorem mixed_004_142_valid : mixed_004_142.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_142]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_142]
  · intro i; fin_cases i <;> norm_num [mixed_004_142]
  · norm_num [mixed_004_142]
  · norm_num [mixed_004_142, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_142, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_142, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_142, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_142]

def mixed_004_143 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(7/512), (71/5120)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14729797/100000000), (1841923/12500000), (1707607/20000000), (721353/5000000), (721353/5000000), (1039257/6250000), (2064319/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(202861/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5591583/100000000), (91/12500000), (860641/20000000), (529497/12500000), (1/100000000), (5562601/100000000), (29903/25000000)]
    alternative := .zero
    polynomial := [(-222736918941795861392672552146112599336873/393897268448094171248785063954687500000000), (75031433187/910000000), (-20125819432278141790174383612566031592013563057/6696253563617600911229346087229687500000000), (75031433187/910000000), (-2515254113082016407566338522397443459728104527/837031695452200113903668260903710937500000)]
    bernstein := [(514704015602535859230800161551208982529345223829/4424644624840161748263052400018010931200000000000000), (24972637879134948202203119442639863880639247287931/191734600409740342424732270667447140352000000000000000), (2157989014324246011809478139522862001785192485403123/17256114036876630818225904360070242631680000000000000000), (1931886494000162930649294714238239535676105818479547/19173460040974034242473227066744714035200000000000000000), (32988706421205952960436742547699020365506829766218513/575203801229221027274196812002341421056000000000000000000)]
    reserve := (11470267/200000000000) }

theorem mixed_004_143_valid : mixed_004_143.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_143]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_143]
  · intro i; fin_cases i <;> norm_num [mixed_004_143]
  · norm_num [mixed_004_143]
  · norm_num [mixed_004_143, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_143, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_143, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_143, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_143]

def mixed_004_144 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(71/5120), (9/640)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(3683321/25000000), (1842379/12500000), (2134709/25000000), (14426233/100000000), (14426233/100000000), (4156431/25000000), (8255329/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(51447/12500000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1118287/20000000), (91/12500000), (538013/12500000), (4235899/100000000), (1/100000000), (695251/12500000), (121269/100000000)]
    alternative := .zero
    polynomial := [(-11610516923214590077015203877009032053428813/19952548603924155944757294387450000000000000), (5437742279/65000000), (-29995553426312536149817274763583655633312428813/9976274301962077972378647193725000000000000), (5437742279/65000000), (-59979496335701857709557534323290302234571428813/19952548603924155944757294387450000000000000)]
    bernstein := [(1614927007009251547623924152607679762460264784882564947/13711286996112753127541849928246736453632000000000000000000), (225727762368247500663766795062428613872557173732958013/1713910874514094140942731241030842056704000000000000000000), (81309988100612527389694316940368201592589711320950681/642716577942785302853524215386565771264000000000000000000), (2736909817615194845521882630312779791033190044650333/26779857414282720952230175641106907136000000000000000000), (196746620701339764566088534752427921473572437100307/3347482176785340119028771955138363392000000000000000000)]
    reserve := (14693627/250000000000) }

theorem mixed_004_144_valid : mixed_004_144.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_144]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_144]
  · intro i; fin_cases i <;> norm_num [mixed_004_144]
  · norm_num [mixed_004_144]
  · norm_num [mixed_004_144, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_144, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_144, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_144, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_144]

def mixed_004_145 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(9/640), (73/5120)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14736771/100000000), (14742681/100000000), (2134909/25000000), (7212703/50000000), (7212703/50000000), (3324667/20000000), (3301353/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(208717/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(698911/12500000), (91/12500000), (4305003/100000000), (2117911/50000000), (1/100000000), (1112283/20000000), (4917/4000000)]
    alternative := .zero
    polynomial := [(-50827535361664215410367700370335763757803/84912051609185438174073116580000000000000), (3089065075197/36400000000), (-127701506303076385103517691876762734753320303/42456025804592719087036558290000000000000), (3089065075197/36400000000), (-255352185070791105991625016053155133742882803/84912051609185438174073116580000000000000)]
    bernstein := [(1698628690388258160104016064054293421272115823917/14245878308504516803010702766558412800000000000000000), (15177446468315793231694908172569599430793992048749/113967026468036134424085622132467302400000000000000000), (350074394309446680509120760120226138492013239517959/2735208635232867226178054931179215257600000000000000000), (44483657460591487387266424522394684361181564863773/429052334938488976655381165675171020800000000000000000), (206789069581226357496440811307347076063850128575581/3432418679507911813243049325401368166400000000000000000)]
    reserve := (481967/8000000000) }

theorem mixed_004_145_valid : mixed_004_145.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_145]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_145]
  · intro i; fin_cases i <;> norm_num [mixed_004_145]
  · norm_num [mixed_004_145]
  · norm_num [mixed_004_145, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_145, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_145, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_145, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_145]

def mixed_004_146 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(73/5120), (37/2560)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14740257/100000000), (14746333/100000000), (8540437/100000000), (14424577/100000000), (14424577/100000000), (3324189/20000000), (16502873/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(211647/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5591141/100000000), (91/12500000), (4305903/100000000), (847149/20000000), (1/100000000), (2780411/50000000), (124581/100000000)]
    alternative := .zero
    polynomial := [(-9663005613803028933932105404202811154054157/15699028799001380128401845885460000000000000), (89515178057/1040000000), (-307052278618579771297084267650197276698379941541/102043687193508970834611998255490000000000000), (89515178057/1040000000), (-613978938164180103218027417930139916851757179041/204087374387017941669223996510980000000000000)]
    bernstein := [(16926345928515023144345529897845332572152784236354889919/140247775763000017029528434354092352785612800000000000000000), (449574092981827286505101363691516173195329032909795191/3339232756261905167369724627478389352038400000000000000000), (13616118765972699158681411954217336635030280188102499877/105185831822250012772146325765569264589209600000000000000000), (87764660363421594806853373188727672263358061210575151/834808189065476291842431156869597338009600000000000000000), (540687669680671329067847945836766829703559504338751599/8765485985187501064345527147130772049100800000000000000000)]
    reserve := (61683707/1000000000000) }

theorem mixed_004_146_valid : mixed_004_146.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_146]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_146]
  · intro i; fin_cases i <;> norm_num [mixed_004_146]
  · norm_num [mixed_004_146]
  · norm_num [mixed_004_146, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_146, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_146, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_146, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_146]

def mixed_004_147 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(37/2560), (15/1024)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14743743/100000000), (14749987/100000000), (4270619/50000000), (3605937/25000000), (3605937/25000000), (16618553/100000000), (16498983/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(429157/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1118199/20000000), (91/12500000), (1076701/25000000), (1058917/25000000), (1/100000000), (1390057/25000000), (31559/25000000)]
    alternative := .zero
    polynomial := [(-1009419069797413310097263836917496520749843/1595448126248829699996076118100000000000000), (907726098601/10400000000), (-26414497501358437083655521491298912191174685773/8774964694368563349978418649550000000000000), (907726098601/10400000000), (-52817891392949102620899973080391731920621123273/17549929388737126699956837299100000000000000)]
    bernstein := [(92068115871989430878274469350896832441141923775464647/753763727717352299173230208112274702336000000000000000000), (8206921393101286446239033295558531585345525459290737/60301098217388183933858416648981976186880000000000000000), (47365987563816566483638752973466825726762449006657213/361806589304329103603150499893891857121280000000000000000), (1028427061303389499810821847537384828378172512524473/9648175714782109429417346663837116189900800000000000000), (93708923257223516592749679867822998814128052639379/1484334725351093758371899486744171721523200000000000000)]
    reserve := (31565967/500000000000) }

theorem mixed_004_147_valid : mixed_004_147.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_147]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_147]
  · intro i; fin_cases i <;> norm_num [mixed_004_147]
  · norm_num [mixed_004_147]
  · norm_num [mixed_004_147, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_147, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_147, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_147, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_147]

def mixed_004_148 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(15/1024), (19/1280)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14747229/100000000), (14753643/100000000), (8542039/100000000), (7211459/50000000), (7211459/50000000), (103851/625000), (8247547/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(435023/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5590849/100000000), (729/100000000), (861541/20000000), (4235591/100000000), (1/100000000), (2779817/50000000), (12789/10000000)]
    alternative := .zero
    polynomial := [(-47676197166995781770021574647306875033927399/73437106250689635630388011289008750000000000), (2147407961947/24300000000), (-110423795458636010425589292749025160766681133649/36718553125344817815194005644504375000000000), (2147407961947/24300000000), (-220799914720105025069408563923403014658328339899/73437106250689635630388011289008750000000000)]
    bernstein := [(9980360679672197982481567647538847550294656962557701/80744952232854825594540250182853474690007040000000000000), (2776217225431335096094727628719060607998695291911101/20186238058213706398635062545713368672501760000000000000), (50088501563341996493631167354115227641821087787016711/378491963591506994974407422732125662609408000000000000000), (3407180378877737793804767071139627299853682883809061/31540996965958916247867285227677138550784000000000000000), (439062470751917724573928719029053750438641956620249/6797628656456662984454156299068348825600000000000000000)]
    reserve := (32295267/500000000000) }

theorem mixed_004_148_valid : mixed_004_148.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_148]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_148]
  · intro i; fin_cases i <;> norm_num [mixed_004_148]
  · norm_num [mixed_004_148]
  · norm_num [mixed_004_148, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_148, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_148, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_148, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_148]

def mixed_004_149 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(19/1280), (77/5120)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(7375357/50000000), (7378651/50000000), (8542839/100000000), (14422087/100000000), (14422087/100000000), (3322753/20000000), (16491207/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(440891/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(349419/6250000), (729/100000000), (2154303/50000000), (4235513/100000000), (1/100000000), (5559039/100000000), (129543/100000000)]
    alternative := .zero
    polynomial := [(-1205386533678423133488564324798166206049/1807593973018400993977400535000000000000), (408150363493/4556250000), (-100706479800349499242450100061811685988187/33473962463303722110692602500000000000), (408150363493/4556250000), (-5436944522685194535958816839013032877156049/1807593973018400993977400535000000000000)]
    bernstein := [(20924854682776420066760204091299906512716033899/167318038762084885244543712519782400000000000000000), (2697652394385712470997397943643205452522375641793/19408892496401846688367070652294758400000000000000000), (494624542049603086086383269426694327960206373539/3696931904076542226355632505199001600000000000000000), (1172225809352677430039954268462603090976301113013/10708354480773432655650797601266073600000000000000000), (82002585128508233302901691842465319927519118860191/1242169119769718188055492521746864537600000000000000000)]
    reserve := (16503909/250000000000) }

theorem mixed_004_149_valid : mixed_004_149.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_149]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_149]
  · intro i; fin_cases i <;> norm_num [mixed_004_149]
  · norm_num [mixed_004_149]
  · norm_num [mixed_004_149, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_149, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_149, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_149, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_149]

def mixed_004_150 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(77/5120), (39/2560)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14754199/100000000), (7380481/50000000), (213591/2500000), (2884251/20000000), (2884251/20000000), (2076421/12500000), (16487321/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(446763/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(34941/625000), (729/100000000), (1077377/25000000), (1058859/25000000), (1/100000000), (1389611/25000000), (26239/20000000)]
    alternative := .zero
    polynomial := [(-47139975404939622430076013007478175242521/68844712996014418358712929700000000000000), (275778757501/3037500000), (-103601298233314300901579286807881306496642521/34422356498007209179356464850000000000000), (275778757501/3037500000), (-23017272943469295797858721955861681646449169/7649412555112713150968103300000000000000)]
    bernstein := [(5985571627512066349605409109731377837671099251524439/47309726531262096831221444754215534592000000000000000000), (369184659169053102461518375684137897084462570699997/2628318140625672046178969153011974144000000000000000000), (685692644997801048697871619171738283850793613435819/5068899271206653231916583366523092992000000000000000000), (656123267749759712560658451640707878930167197581677/5913715816407762103902680594276941824000000000000000000), (199555004601234538203781971105210086235998686940039/2956857908203881051951340297138470912000000000000000000)]
    reserve := (67488871/1000000000000) }

theorem mixed_004_150_valid : mixed_004_150.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_150]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_150]
  · intro i; fin_cases i <;> norm_num [mixed_004_150]
  · norm_num [mixed_004_150]
  · norm_num [mixed_004_150, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_150, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_150, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_150, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_150]

def mixed_004_151 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(39/2560), (79/5120)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(3689421/25000000), (922789/6250000), (4272221/50000000), (7210211/50000000), (7210211/50000000), (1660897/10000000), (4120859/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(452637/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1118083/20000000), (729/100000000), (431041/10000000), (2117679/50000000), (1/100000000), (5557849/100000000), (66423/50000000)]
    alternative := .zero
    polynomial := [(-4563846655785867161993695400989721740850629/6493295190943945913322800776770000000000000), (93153443933/1012500000), (-9775414350206527687057483330541615880988250629/3246647595471972956661400388385000000000000), (93153443933/1012500000), (-19546264853757269506952972965682242040235650629/6493295190943945913322800776770000000000000)]
    bernstein := [(35694410899993728043819222350852174065054895337150811/278884904883783230669142800273505465139200000000000000000), (121242131434429653145042586672280548251483792594607/854165099184634703427696172353768652800000000000000000), (35204348725966181313900570342287280701581210001345861/257432219892722982156131815637081967820800000000000000000), (384095914532781952005642663896628991235022646864447/3416660396738538813710784689415074611200000000000000000), (307629774526447590292250787135479242787197431506745851/4462158478140531690706284804376087442227200000000000000000)]
    reserve := (430887/6250000000) }

theorem mixed_004_151_valid : mixed_004_151.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_151]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_151]
  · intro i; fin_cases i <;> norm_num [mixed_004_151]
  · norm_num [mixed_004_151]
  · norm_num [mixed_004_151, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_151, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_151, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_151, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_151]

def mixed_004_152 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(79/5120), (1/64)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14761169/100000000), (461509/3125000), (8545243/100000000), (14419589/100000000), (14419589/100000000), (16606571/100000000), (257493/1562500)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(229257/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(21837/390625), (729/100000000), (4311313/100000000), (52941/1250000), (1/100000000), (5557253/100000000), (134497/100000000)]
    alternative := .zero
    polynomial := [(-4298925457836215446060897611407182060548521/5960564846521237225009794657600000000000000), (3932577541/42187500), (-727141520258150905199683544864018281939416430201/241402876284110107612896683632800000000000000), (3932577541/42187500), (-1453934827554217076948236157021512582131928430201/482805752568220215225793367265600000000000000)]
    bernstein := [(42953542179230558128671429119804042886478755139208542919/331781586816187813331338202889515031330816000000000000000000), (594822036563419202036568270144693095593586668257052681/4147269835202347666641727536118937891635200000000000000000), (21498821262695691417264417916762284180697205770271861/155522618820088037499064782604460170936320000000000000000), (73805961389643276423578742493518626930991759556777/648010911750366822912769927518584045568000000000000000), (570293086684895970295850968516369656340412262791/8100136396879585286409624093982300569600000000000000)]
    reserve := (8800671/125000000000) }

theorem mixed_004_152_valid : mixed_004_152.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_152]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_152]
  · intro i; fin_cases i <;> norm_num [mixed_004_152]
  · norm_num [mixed_004_152]
  · norm_num [mixed_004_152, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_152, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_152, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_152, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_152]

def mixed_004_153 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/64), (81/5120)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14764653/100000000), (2954391/20000000), (2136511/25000000), (7209377/50000000), (7209377/50000000), (1660417/10000000), (1647567/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(232197/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5590129/100000000), (729/100000000), (539027/12500000), (2117601/50000000), (1/100000000), (347291/6250000), (136147/100000000)]
    alternative := .zero
    polynomial := [(-5022300761960566155956665785255127567899937/6788293416780820543480913232547500000000000), (76489208857/810000000), (-10227856699022794346420748687048703827793712437/3394146708390410271740456616273750000000000), (76489208857/810000000), (-20450691097283628126685540708312152528019524937/6788293416780820543480913232547500000000000)]
    bernstein := [(552258229944873907105304275747945238011657621/4218098700915179663526543451100282880000000000000), (20955333240596215166265817547214701013840361817/144620526888520445606624346894866841600000000000000), (305505496191473399926045249244299088320786357902917/2186662366554429137572160125050386644992000000000000000), (961039454854022241101271334461904905548503040509889/8330142348778777666941562381144330076160000000000000000), (335245501545510317996223210758759935598315348425576823/4664879715316115493487274933440824842649600000000000000000)]
    reserve := (898323/12500000000) }

theorem mixed_004_153_valid : mixed_004_153.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_153]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_153]
  · intro i; fin_cases i <;> norm_num [mixed_004_153]
  · norm_num [mixed_004_153]
  · norm_num [mixed_004_153, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_153, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_153, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_153, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_153]

def mixed_004_154 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(81/5120), (41/2560)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14768137/100000000), (14775623/100000000), (1709369/20000000), (14417919/100000000), (14417919/100000000), (2075221/12500000), (1647179/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(470277/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2794993/50000000), (73/10000000), (26957/625000), (4235123/100000000), (1/100000000), (277803/5000000), (34449/25000000)]
    alternative := .zero
    polynomial := [(-5630101688965762829728752737774550062328703/7430763984728087309228318447100000000000000), (6972684470971/73000000000), (-11185221361484178743431383585531276583421178703/3715381992364043654614159223550000000000000), (6972684470971/73000000000), (-22364812621279391724033038418324778616780028703/7430763984728087309228318447100000000000000)]
    bernstein := [(676080615784145971826476310132074642797753100963656737/5106382127792284551322922676378880966656000000000000000000), (373648979322841019547773362735005913569217716395963257/2553191063896142275661461338189440483328000000000000000000), (540583339410571803975445576299759916718133853174926131/3829786595844213413492192007284160724992000000000000000000), (74564899303810292012453445400717301022275581485157097/638297765974035568915365334547360120832000000000000000000), (23407578679445279741954031883738034149934862221852417/319148882987017784457682667273680060416000000000000000000)]
    reserve := (36671879/500000000000) }

theorem mixed_004_154_valid : mixed_004_154.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_154]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_154]
  · intro i; fin_cases i <;> norm_num [mixed_004_154]
  · norm_num [mixed_004_154]
  · norm_num [mixed_004_154, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_154, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_154, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_154, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_154]

def mixed_004_155 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(41/2560), (83/5120)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14771621/100000000), (14779293/100000000), (8547647/100000000), (14417083/100000000), (14417083/100000000), (4149841/25000000), (1646791/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(238081/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1397461/25000000), (73/10000000), (539253/12500000), (847009/20000000), (1/100000000), (5555463/100000000), (27889/20000000)]
    alternative := .zero
    polynomial := [(-276512557189067989294961548726369833817771/355982298327373466160105504525000000000000), (3530690431033/36500000000), (-536066807132677255398000346362678161039580271/177991149163686733080052752262500000000000), (3530690431033/36500000000), (-1071857101708165442806705731176629952245342771/355982298327373466160105504525000000000000)]
    bernstein := [(2046998928105208362476389058006044094679009227849069/15289323292709845387358158418444550144000000000000000000), (136988609169877401438425288869619217401515234470559/926625654103626993173221722329972736000000000000000000), (26170350676545199159467396537375721410552445060532783/183471879512518144648297901021334601728000000000000000000), (438460049656677525647705190159635771648327838377671/3706502616414507972692886889319890944000000000000000000), (18298635058851373906444435214653529315244976557425309/244629172683357526197730534695112802304000000000000000000)]
    reserve := (18700381/250000000000) }

theorem mixed_004_155_valid : mixed_004_155.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_155]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_155]
  · intro i; fin_cases i <;> norm_num [mixed_004_155]
  · norm_num [mixed_004_155]
  · norm_num [mixed_004_155, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_155, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_155, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_155, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_155]

def mixed_004_156 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(83/5120), (21/1280)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(230861/1562500), (7391483/50000000), (267139/3125000), (7208123/50000000), (7208123/50000000), (8298479/50000000), (514501/3125000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(482051/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2794851/50000000), (73/10000000), (4314929/100000000), (2117483/50000000), (1/100000000), (1110973/20000000), (35273/25000000)]
    alternative := .zero
    polynomial := [(-2907741233048368268140611709045340294430204151/3652506631876703772834282131073450000000000000), (3575090514993/36500000000), (-5502523274998658534110413774960596561535863004151/1826253315938351886417141065536725000000000000), (3575090514993/36500000000), (-11002138808764268699952686938212147782777295804151/3652506631876703772834282131073450000000000000)]
    bernstein := [(339727139130578179266393338152177499544522250431018066329/2509983445173368609376488796895624499822592000000000000000000), (93696971142766980239628477602767392845833985001407025823/627495861293342152344122199223906124955648000000000000000000), (9690189372902436099949589663236370264289190301193661229/67231699424286659179727378488275656245248000000000000000000), (4697878748918376607423764621149353870464373245462251087/39218491330833884521507637451494132809728000000000000000000), (747964563845755550449879929643365232088963477285760569/9804622832708471130376909362873533202432000000000000000000)]
    reserve := (4767933/62500000000) }

theorem mixed_004_156_valid : mixed_004_156.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_156]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_156]
  · intro i; fin_cases i <;> norm_num [mixed_004_156]
  · norm_num [mixed_004_156]
  · norm_num [mixed_004_156, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_156, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_156, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_156, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_156]

def mixed_004_157 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(21/1280), (17/1024)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14778587/100000000), (184833/1250000), (34197/400000), (900963/6250000), (900963/6250000), (16594551/100000000), (3292031/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(243971/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5589561/100000000), (73/10000000), (2157917/50000000), (4234887/100000000), (1/100000000), (5554267/100000000), (142739/100000000)]
    alternative := .zero
    polynomial := [(-26792978660022839219283338183768869577350171109/32847628209008187736006265853105900000000000000), (361952726059/3650000000), (-49505803445390208312466906703074126753580624671109/16423814104504093868003132926552950000000000000), (361952726059/3650000000), (-98984813912120393785714530067964484637583899171109/32847628209008187736006265853105900000000000000)]
    bernstein := [(12065423160627992295347430353713332230732304338539211371/88174680568035761826484495931357112827904000000000000000000), (10638294272950826485295797828246893943405211399945701487/70539744454428609461187596745085690262323200000000000000000), (24653802867689303810618552550098973762605177151917346793/169295386690628662706850232188205656629575680000000000000000), (12303383500376067572299672008327509387418368069455699/101450418990638899000359689700797397231206400000000000000), (1262193087607899363452513302452627756041292155658251/16232067038502223840057550352127583556993024000000000000)]
    reserve := (77759233/1000000000000) }

theorem mixed_004_157_valid : mixed_004_157.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_157]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_157]
  · intro i; fin_cases i <;> norm_num [mixed_004_157]
  · norm_num [mixed_004_157]
  · norm_num [mixed_004_157, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_157, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_157, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_157, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_157]

def mixed_004_158 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(17/1024), (43/2560)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(1478207/10000000), (14790317/100000000), (8550051/100000000), (14414569/100000000), (14414569/100000000), (16592143/100000000), (411407/2500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(123459/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5589421/100000000), (73/10000000), (4316739/100000000), (529351/12500000), (1/100000000), (5553669/100000000), (28877/20000000)]
    alternative := .zero
    polynomial := [(-4164357234780645982625248561479101805712126561/4984252341057596513751027952622700000000000000), (1832004288703/18250000000), (-7515091129210795147003823296769405816727356626561/2492126170528798256875513976311350000000000000), (1832004288703/18250000000), (-15026017901186809648025021344977332531649001126561/4984252341057596513751027952622700000000000000)]
    bernstein := [(30320485415390357177060276645045970663662242129418231/219209736190503066408184620471258459414724608000000000000), (139111443777694033933724921953987283088940804859160779/913373900793762776700769251963576914228019200000000000000), (15117320580757053793861730206661912353293403045525390613/102754563839298312378836540845902402850652160000000000000000), (85464484433630527817493678930135803758198195971485447/696169131702563091997537539606384843161600000000000000000), (413705784338957782932053229754016397926397706676838679/5221268487769223189981531547047886323712000000000000000000)]
    reserve := (79234727/1000000000000) }

theorem mixed_004_158_valid : mixed_004_158.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_158]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_158]
  · intro i; fin_cases i <;> norm_num [mixed_004_158]
  · norm_num [mixed_004_158]
  · norm_num [mixed_004_158, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_158, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_158, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_158, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_158]

def mixed_004_159 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(43/2560), (87/5120)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14785553/100000000), (3698499/25000000), (8550853/100000000), (1441373/10000000), (1441373/10000000), (16589733/100000000), (8226203/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(499733/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5589281/100000000), (73/10000000), (2158823/50000000), (4234729/100000000), (1/100000000), (555307/10000000), (146031/100000000)]
    alternative := .zero
    polynomial := [(-8626584555504330025721679845308743409064145277/10082736470556558881925941940356900000000000000), (1854267128957/18250000000), (-15208823309533169402961908415698083827309763345277/5041368235278279440962970970178450000000000000), (1854267128957/18250000000), (-30409020034510834475898095151550858911210462545277/10082736470556558881925941940356900000000000000)]
    bernstein := [(60541291352111071332116858589383260885910703206892581523/433050233952268873161702461278276680679424000000000000000000), (133208142263817714604254148451251439945267801443353895007/866100467904537746323404922556553361358848000000000000000000), (772330143711765382680205384784424581848353329225197763089/5196602807427226477940429535339320168153088000000000000000000), (430492259130337422823718226104174404551989306052775991367/3464401871618150985293619690226213445435392000000000000000000), (559296783747946012659531267669817334152227298287206616803/6928803743236301970587239380452426890870784000000000000000000)]
    reserve := (4036027/50000000000) }

theorem mixed_004_159_valid : mixed_004_159.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_159]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_159]
  · intro i; fin_cases i <;> norm_num [mixed_004_159]
  · norm_num [mixed_004_159]
  · norm_num [mixed_004_159, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_159, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_159, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_159, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_159]

def mixed_004_160 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(87/5120), (11/640)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(2957807/20000000), (3699419/25000000), (1710331/20000000), (1441289/10000000), (1441289/10000000), (16587321/100000000), (16448533/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(15801/3125000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5589141/100000000), (731/100000000), (539819/12500000), (84693/2000000), (1/100000000), (5552471/100000000), (5907/4000000)]
    alternative := .zero
    polynomial := [(-166786814507723740945532631176481693460343/190678036090609851469424423300000000000000), (87281700773/850000000), (-287349700299158130835850203661069703278800343/95339018045304925734712211650000000000000), (87281700773/850000000), (-574532613783808537930754874690962924864140343/190678036090609851469424423300000000000000)]
    bernstein := [(18514966757354198148566280758306906425304063634182377/131032948651948320761055270722745663488000000000000000000), (363301503725708974399665090230769362037982313606883/2339874083070505727875986977191886848000000000000000000), (83795087249655129805828881454373475222683604208889/558379042550916139606769619557154816000000000000000000), (4595990689957615054284602604429985290885092145947/36560532547976651998062296518623232000000000000000000), (154658909501234274252745280502943646553757123561/1881792116439974735194382909046784000000000000000000)]
    reserve := (10273379/125000000000) }

theorem mixed_004_160_valid : mixed_004_160.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_160]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_160]
  · intro i; fin_cases i <;> norm_num [mixed_004_160]
  · norm_num [mixed_004_160]
  · norm_num [mixed_004_160, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_160, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_160, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_160, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_160]

def mixed_004_161 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(11/640), (89/5120)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14792517/100000000), (14801359/100000000), (1069057/12500000), (900753/6250000), (900753/6250000), (16584909/100000000), (8222331/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(102307/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2794501/50000000), (731/100000000), (4319459/100000000), (4234571/100000000), (1/100000000), (5551871/100000000), (149319/100000000)]
    alternative := .zero
    polynomial := [(-924353965452417653823472730134374732648517831873/1032508429477353252404595223614419700000000000000), (7595455271909/73100000000), (-1556640089758915824333177554881271990717356125331873/516254214738676626202297611807209850000000000000), (7595455271909/73100000000), (-3112355825552379231012531637032409606702063732831873/1032508429477353252404595223614419700000000000000)]
    bernstein := [(1902626659248076684991194088692609233403587293227624139/13325089956278709710688010353190323093504000000000000000000), (5570477688276742446890887841703129102099260831605812787/35533573216743225895168027608507528249344000000000000000000), (5041381431252046680601247105993461778684351227739458535621/33259424530871659437877273841563046441385984000000000000000000), (3761060164495622081858806612967845154753377372730209084831/29563932916330363944779798970278263503454208000000000000000000), (59379079045360304584764465123026661334915608881620595522207/709534389991928734674715175286678324082900992000000000000000000)]
    reserve := (41843693/500000000000) }

theorem mixed_004_161_valid : mixed_004_161.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_161]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_161]
  · intro i; fin_cases i <;> norm_num [mixed_004_161]
  · norm_num [mixed_004_161]
  · norm_num [mixed_004_161, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_161, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_161, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_161, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_161]

def mixed_004_162 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(89/5120), (9/512)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14795999/100000000), (3701261/25000000), (4276629/50000000), (7205603/50000000), (7205603/50000000), (8291247/50000000), (2055099/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1617/312500), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(43663/781250), (731/100000000), (4320367/100000000), (4234491/100000000), (1/100000000), (5551271/100000000), (75481/50000000)]
    alternative := .zero
    polynomial := [(-179303576601282068402688668000867647358768720657/195736971504695452151249657289592800000000000000), (480297400329/4568750000), (-295224757434337417005096630363766494852476288720657/97868485752347726075624828644796400000000000000), (480297400329/4568750000), (-14396834421757891510775379806330051757502288017577/4774072475724279320762186763160800000000000000)]
    bernstein := [(1141615759406259815746925261818644354623756699808672030239/7912318976289420022866354104376556020301824000000000000000000), (2128913264229013009043318351807429553143567298921552505823/13450942259692014038872801977440145234513100800000000000000000), (617732905609058238803919963915479014504562565860800969741/4035282677907604211661840593232043570353930240000000000000000), (692533373946972899609540322089491269254431035151237207/5380376903876805615549120790976058093805240320000000000000), (107819466747007382608296396286522165290703965604559/1265971036206307203658616656700248963248291840000000000)]
    reserve := (21291851/250000000000) }

theorem mixed_004_162_valid : mixed_004_162.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_162]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_162]
  · intro i; fin_cases i <;> norm_num [mixed_004_162]
  · norm_num [mixed_004_162]
  · norm_num [mixed_004_162, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_162, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_162, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_162, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_162]

def mixed_004_163 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(9/512), (23/1280)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14801221/100000000), (592423/4000000), (8554461/100000000), (7204971/50000000), (7204971/50000000), (1657887/10000000), (16434989/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(526303/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5588657/100000000), (731/50000000), (4321729/100000000), (1058593/25000000), (1/100000000), (555037/10000000), (19277/12500000)]
    alternative := .zero
    polynomial := [(-38423409408292551054621355046422612453760279/81070396780605055826895601452345000000000000), (461347409533/8600000000), (-61533729656648061704485301670755126617645666529/40535198390302527913447800726172500000000000), (461347409533/8600000000), (-123029035903887830857915981986463830622837572779/81070396780605055826895601452345000000000000)]
    bernstein := [(1661176955147412864696576663329251478009392529/14171358335244714607059671929043306938368000000000), (81272523617471656581181501777455876776708217553123/557111524554307842990033352710515004014592000000000000), (14199871879822773304044804936676910339754352091221663/104458410853932720560631253633221563252736000000000000000), (7607024657049040813377485920968824028512443706532203/87048675711610600467192711361017969377280000000000000000), (50385469583950215749523972373419844201179191523061/217621689279026501167981778402544923443200000000000000000)]
    reserve := (231527/1000000000000) }

theorem mixed_004_163_valid : mixed_004_163.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_163]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_163]
  · intro i; fin_cases i <;> norm_num [mixed_004_163]
  · norm_num [mixed_004_163]
  · norm_num [mixed_004_163, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_163, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_163, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_163, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_163]

def mixed_004_164 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(23/1280), (47/2560)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14808183/100000000), (7408979/50000000), (4278033/50000000), (3602063/25000000), (3602063/25000000), (1035877/6250000), (16427257/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(538131/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5588383/100000000), (1463/100000000), (4323547/100000000), (4234211/100000000), (1/100000000), (5549167/100000000), (157497/100000000)]
    alternative := .zero
    polynomial := [(-134940947055857608934867142021410573370086181263/272522279420654973390178613091657931250000000000), (9115987171/166250000), (-620582440736221169602056957813844923571709148856289/408783419130982460085267919637486896875000000000), (9115987171/166250000), (-1240760058631274766377309314201625615423308039168789/817566838261964920170535839274973793750000000000)]
    bernstein := [(263855866177453742661652698032632531837913851728095416651/2194639270393288008019813857801202997133312000000000000000000), (653495413342869763002759367456101782240292646095114532739/4389278540786576016039627715602405994266624000000000000000000), (47518479039999820707633761419934814931267136118534086069/342021704476876053197893068748239428124672000000000000000000), (122056426882372890148352314795557617595445196540549024063/1350547243318946466473731604800740305928192000000000000000000), (8664879576877301673333378217074504070990170406630822807/2701094486637892932947463209601480611856384000000000000000000)]
    reserve := (1603957/500000000000) }

theorem mixed_004_164_valid : mixed_004_164.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_164]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_164]
  · intro i; fin_cases i <;> norm_num [mixed_004_164]
  · norm_num [mixed_004_164]
  · norm_num [mixed_004_164, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_164, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_164, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_164, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_164]

def mixed_004_165 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(47/2560), (3/160)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(1851893/12500000), (3706337/25000000), (855767/10000000), (90041/625000), (90041/625000), (4142297/25000000), (1641953/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(54997/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5588111/100000000), (1463/100000000), (4325367/100000000), (4234051/100000000), (1/100000000), (5547963/100000000), (80387/50000000)]
    alternative := .zero
    polynomial := [(-95929013661168556090904703438334067605883831413/185483496599588141732211825359385725000000000000), (410077009217/7315000000), (-140898138999971497026242335321521762779653413331413/92741748299794070866105912679692862500000000000), (410077009217/7315000000), (-281700348986281825496393765939605191491700942831413/185483496599588141732211825359385725000000000000)]
    bernstein := [(981931864888874849554326431958263557805663156047465118347/7966455518429582758092625796630251355242496000000000000000000), (6877757408232578644277731205884988462573325930904046573/45263951809258992943708101117217337245696000000000000000000), (401720645811663473590303906228916414217284658553715177/2828996988078687058981756319826083577856000000000000000000), (181690767593506921138789127119443002465494822578808903/1944935429304097353049957469880432459776000000000000000000), (753152060312849058403276057009655731509283291865147/121558464331506084565622341867527028736000000000000000000)]
    reserve := (6195801/1000000000000) }

theorem mixed_004_165_valid : mixed_004_165.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_165]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_165]
  · intro i; fin_cases i <;> norm_num [mixed_004_165]
  · norm_num [mixed_004_165]
  · norm_num [mixed_004_165, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_165, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_165, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_165, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_165]

def mixed_004_166 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/160), (49/2560)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14822103/100000000), (14832747/100000000), (342371/4000000), (56269/390625), (56269/390625), (8282169/50000000), (512869/3125000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(28091/5000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5587841/100000000), (183/12500000), (4327189/100000000), (4233889/100000000), (1/100000000), (5546757/100000000), (164049/100000000)]
    alternative := .zero
    polynomial := [(-51079498078173468669199170355274189325129957719/94706695698177944020477844588747550000000000000), (698448974447/12200000000), (-482869001646953067027445637007262569601310613181/317807703685160885974757867747475000000000000), (698448974447/12200000000), (-143843882992713840505509600657808971551865432770219/94706695698177944020477844588747550000000000000)]
    bernstein := [(7838368672621585487818814876103043830719455864857061/62066980092757897393260360229681594368000000000000000000), (153896437004777647514460062202869413172306919190097863/993071681484126358292165763674905509888000000000000000000), (113317300187326962127095492486343847485568932693389667/781433454282591232754491092727794499584000000000000000000), (24510964792585618274611591337031586148950795681679367407/254226350459936347722794435500775810531328000000000000000000), (37319577988349646055074726138453195979636770333391701781/4067621607358981563564710968012412968501248000000000000000000)]
    reserve := (917479/100000000000) }

theorem mixed_004_166_valid : mixed_004_166.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_166]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_166]
  · intro i; fin_cases i <;> norm_num [mixed_004_166]
  · norm_num [mixed_004_166]
  · norm_num [mixed_004_166, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_166, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_166, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_166, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_166]

def mixed_004_167 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(49/2560), (5/256)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(7414531/50000000), (2968031/20000000), (107011/1250000), (3600791/25000000), (3600791/25000000), (8279741/50000000), (4101023/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(286841/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5587573/100000000), (293/20000000), (4329013/100000000), (4233727/100000000), (1/100000000), (110911/2000000), (4183/2500000)]
    alternative := .zero
    polynomial := [(-5956751062033102082365365931468778508036613/10599614956027832813384408284650000000000000), (856159379027/14650000000), (-8053126525176145282613645509005907828176186613/5299807478013916406692204142325000000000000), (856159379027/14650000000), (-16100296299290257463144925652080346877844336613/10599614956027832813384408284650000000000000)]
    bernstein := [(58876835422616976512477039113205509692654394678007387/455249995863320199992417046588832088064000000000000000000), (479555308226070260914808534400512162017612142659609/3034999972422134666616113643925547253760000000000000000), (2021928866396391741341799141869227361341785913360457/13657499875899605999772511397664962641920000000000000000), (3017962726317322049418568769597363433188044581649/30349999724221346666161136439255472537600000000000000), (554832371248985544290491618417246916049150530027/45524999586332019999241704658883208806400000000000000)]
    reserve := (12187421/1000000000000) }

theorem mixed_004_167_valid : mixed_004_167.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_167]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_167]
  · intro i; fin_cases i <;> norm_num [mixed_004_167]
  · norm_num [mixed_004_167]
  · norm_num [mixed_004_167, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_167, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_167, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_167, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_167]

def mixed_004_168 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(5/256), (51/2560)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14836019/100000000), (1484757/10000000), (4281243/50000000), (7200731/50000000), (7200731/50000000), (16554621/100000000), (16396381/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(117111/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5587307/100000000), (293/20000000), (4330839/100000000), (846713/20000000), (1/100000000), (5544341/100000000), (170589/100000000)]
    alternative := .zero
    polynomial := [(-10073489292265763126122410924152154010164286541/17205426342320899458079570205732100000000000000), (6829773631/114453125), (-13082080699201076405919727404375991929733009786541/8602713171160449729039785102866050000000000000), (6829773631/114453125), (-26154087909109887048713332397827831705455855286541/17205426342320899458079570205732100000000000000)]
    bernstein := [(9782695140263501662608113091642856110106220500399939/73896743454005163909755876999355361237401600000000000000), (23809367204662448843443820081498408077020150921485377/147793486908010327819511753998710722474803200000000000000), (478666298347768356575310934500784069088855309778341407/3167003290885935596132394728543801195888640000000000000000), (1515044031210885023833404118221973571581019036413467857/14779348690801032781951175399871072247480320000000000000000), (11236355091827356694153737343504220203315481562868465059/738967434540051639097558769993553612374016000000000000000000)]
    reserve := (380137/25000000000) }

theorem mixed_004_168_valid : mixed_004_168.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_168]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_168]
  · intro i; fin_cases i <;> norm_num [mixed_004_168]
  · norm_num [mixed_004_168]
  · norm_num [mixed_004_168, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_168, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_168, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_168, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_168]

def mixed_004_169 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(51/2560), (13/640)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(463843/3125000), (7427497/50000000), (2141023/25000000), (2879951/20000000), (2879951/20000000), (16549753/100000000), (655547/4000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1867/312500), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1396761/25000000), (733/50000000), (4332667/100000000), (2116701/50000000), (1/100000000), (5543129/100000000), (86927/50000000)]
    alternative := .zero
    polynomial := [(-91855097675184380570901883567335536486958448643/150809716578509176575148932597803100000000000000), (446150960523/7330000000), (-114680193079716249458767627924120396756224529198643/75404858289254588287574466298901550000000000000), (446150960523/7330000000), (-229268531061757314536964353964673457975962099948643/150809716578509176575148932597803100000000000000)]
    bernstein := [(877327287513727097846339735238802331140930797329516658157/6477228006237259298261539518368726359474176000000000000000000), (265836188231325030192345001052067091039960207343216052691/1619307001559314824565384879592181589868544000000000000000000), (187282951471641011369690457733934384056223651205556828999/1214480251169486118424038659694136192401408000000000000000000), (10684600536074569189729321399251694005729895394111498579/101206687597457176535336554974511349366784000000000000000000), (461932754146561219587802247470509908174495806697520877/25301671899364294133834138743627837341696000000000000000000)]
    reserve := (3651401/200000000000) }

theorem mixed_004_169_valid : mixed_004_169.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_169]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_169]
  · intro i; fin_cases i <;> norm_num [mixed_004_169]
  · norm_num [mixed_004_169]
  · norm_num [mixed_004_169, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_169, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_169, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_169, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_169]

def mixed_004_170 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(13/640), (53/2560)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14849931/100000000), (14862427/100000000), (4282849/50000000), (7199023/50000000), (7199023/50000000), (16544879/100000000), (8190487/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(121867/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2793391/50000000), (1467/100000000), (4334497/100000000), (2116619/50000000), (1/100000000), (5541917/100000000), (44279/25000000)]
    alternative := .zero
    polynomial := [(-584124600409190578974193167117922603810845734287/922573682621973511470517503503625300000000000000), (9104258733761/146700000000), (-701635744295084284662145706254281437602611689984287/461286841310986755735258751751812650000000000000), (9104258733761/146700000000), (-1402687363989759378745317219341444952601412534234287/922573682621973511470517503503625300000000000000)]
    bernstein := [(21441112104852319183914759030944553650154433038987751393/154782179492642959482193497880610784411648000000000000000000), (676727325716533026745255247859031356525996492894031761/4046592927912234234828588179885249265664000000000000000000), (1168382741529965400889445578498557828028736427810571820819/7429544615646862055145287898269317651759104000000000000000000), (7031814292007744832375801171420955670467640616213261921/64745486846595747757257410878163988250624000000000000000000), (280921150003891470636767748862721360303653904277268113451/13208079316705532542480511819145453603127296000000000000000000)]
    reserve := (21268887/1000000000000) }

theorem mixed_004_170_valid : mixed_004_170.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_170]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_170]
  · intro i; fin_cases i <;> norm_num [mixed_004_170]
  · norm_num [mixed_004_170]
  · norm_num [mixed_004_170, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_170, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_170, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_170, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_170]

def mixed_004_171 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(53/2560), (27/1280)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(2971377/20000000), (3717467/25000000), (1070913/12500000), (3599083/25000000), (3599083/25000000), (827/5000), (16373279/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(621243/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2793261/50000000), (367/25000000), (542041/12500000), (4233073/100000000), (1/100000000), (5540703/100000000), (90187/50000000)]
    alternative := .zero
    polynomial := [(-21473077571389714108807321206639008290542029/32649143213878572413985132371759750000000000), (2321468338267/36700000000), (-24833485062309022532659478092535806761781810779/16324571606939286206992566185879875000000000), (2321468338267/36700000000), (-49645497047046655351210148863864974515273079529/32649143213878572413985132371759750000000000)]
    bernstein := [(198564693708557332350764475896260836801223608141077351/1402270023460288018332339165669390402191360000000000000000), (119416576405418290150849337866663654206817405549177609/701135011730144009166169582834695201095680000000000000000), (56213171758610774756355730444205098621251292840637831/350567505865072004583084791417347600547840000000000000000), (19577748364428681332625706252682939045325110700356329/175283752932536002291542395708673800273920000000000000000), (2133730834021946893803746578239450970544602200959911/87641876466268001145771197854336900136960000000000000000)]
    reserve := (24346019/1000000000000) }

theorem mixed_004_171_valid : mixed_004_171.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_171]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_171]
  · intro i; fin_cases i <;> norm_num [mixed_004_171]
  · norm_num [mixed_004_171]
  · norm_num [mixed_004_171, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_171, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_171, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_171, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_171]

def mixed_004_172 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(27/1280), (11/512)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(7431919/50000000), (14877317/100000000), (8568911/100000000), (1799327/12500000), (1799327/12500000), (8267557/50000000), (4091397/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(633161/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(698283/12500000), (367/25000000), (2169081/50000000), (1058227/25000000), (1/100000000), (5539487/100000000), (18363/10000000)]
    alternative := .zero
    polynomial := [(-25233737916698255813747130338934472126828849/36936038037594445224199041055350000000000000), (1893557255081/29360000000), (-28116921373284466485379328665785771458950903849/18468019018797222612099520527675000000000000), (1893557255081/29360000000), (-56208609008652234714944910201232608445774978849/36936038037594445224199041055350000000000000)]
    bernstein := [(14347529346661787694996042437322438512066950242135791/99149422134550100468248918204555984896000000000000000000), (6879241969807316895776052956293830921270189117628703/39659768853820040187299567281822393958400000000000000000), (7780718620022992911833351477908601781001674632285933/47591722624584048224759480738186872750080000000000000000), (145697427596592235263835360602853194534749649230771/1269112603322241285993586153018316606668800000000000000), (2781542617109483872288229535839318172861691447559/101529008265779302879486892241465328533504000000000000)]
    reserve := (2739653/100000000000) }

theorem mixed_004_172_valid : mixed_004_172.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_172]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_172]
  · intro i; fin_cases i <;> norm_num [mixed_004_172]
  · norm_num [mixed_004_172]
  · norm_num [mixed_004_172, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_172, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_172, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_172, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_172]

def mixed_004_173 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(11/512), (7/320)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14870789/100000000), (595391/4000000), (4285259/50000000), (224889/1562500), (224889/1562500), (8265111/50000000), (1022369/6250000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(645091/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(698251/12500000), (1469/100000000), (2169999/50000000), (4232743/100000000), (1/100000000), (5538269/100000000), (186883/100000000)]
    alternative := .zero
    polynomial := [(-13289492459373296452316514942916852517892608551/18752332529287212696953254147358925000000000000), (9650093911477/146900000000), (-14276923466114826862579538528842031380624845983551/9376166264643606348476627073679462500000000000), (9650093911477/146900000000), (-28540557439770280428706760542741145908731799358551/18752332529287212696953254147358925000000000000)]
    bernstein := [(7618755877967076844823295807721981216977148304395841/51546019159683546063622518658357086495178752000000000000), (243076923021568186241015801653299347817284328080197/1376763332256504969648037357327913635020800000000000000), (251566711174987924124163743774186994948476487445473587/1510137280068853888582690976319055268413440000000000000000), (317003930411313618387599689411160501307500355850001/2688990883313486268843822963531081318400000000000000000), (5991089825171338636187501459626163136571470515363849/196632458342298683409204554208210321408000000000000000000)]
    reserve := (7617117/250000000000) }

theorem mixed_004_173_valid : mixed_004_173.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_173]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_173]
  · intro i; fin_cases i <;> norm_num [mixed_004_173]
  · norm_num [mixed_004_173]
  · norm_num [mixed_004_173, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_173, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_173, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_173, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_173]

def mixed_004_174 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(7/320), (57/2560)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(743887/5000000), (14892241/100000000), (4286063/50000000), (14391173/100000000), (14391173/100000000), (661013/4000000), (16350223/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(657033/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2792877/50000000), (147/10000000), (868367/20000000), (4232577/100000000), (1/100000000), (110741/2000000), (47533/25000000)]
    alternative := .zero
    polynomial := [(-2593537566930040845049147248174492137537413/3530193173781843906536247444228000000000000), (468226830313/7000000000), (-896028151218814977150781434724802875252497471/588365528963640651089374574038000000000000), (468226830313/7000000000), (-5373575369745959822059639461100642759377447413/3530193173781843906536247444228000000000000)]
    bernstein := [(1862224952938496367635851327373419915572615487929/12338919457971569187133840666929397760000000000000000), (53209973910956251215692890299358022105415781129237/296134066991317660491212176006305546240000000000000000), (402060272718808905149050808774802355765610426671787/2369072535930541283929697408050444369920000000000000000), (2293490357675586002989495477351446177940039534796437/18952580287444330271437579264403554959360000000000000000), (5091547695950921896698220868403357328779322531078187/151620642299554642171500634115228439674880000000000000000)]
    reserve := (16790417/500000000000) }

theorem mixed_004_174_valid : mixed_004_174.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_174]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_174]
  · intro i; fin_cases i <;> norm_num [mixed_004_174]
  · norm_num [mixed_004_174]
  · norm_num [mixed_004_174, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_174, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_174, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_174, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_174]

def mixed_004_175 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(57/2560), (29/1280)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(1488469/10000000), (3724929/25000000), (8573733/100000000), (7194723/50000000), (7194723/50000000), (16520421/100000000), (16342549/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(334493/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2792751/50000000), (147/10000000), (173747/4000000), (423241/10000000), (1/100000000), (5535829/100000000), (96689/50000000)]
    alternative := .zero
    polynomial := [(-16513804147458533930362017873100432357311/21681485683490165723335609100000000000000), (834645708503/12250000000), (-2360457752534635722631176930161683235872473/1548677548820726123095400650000000000000), (834645708503/12250000000), (-33029894731337441582906115004390464869857311/21681485683490165723335609100000000000000)]
    bernstein := [(649122580938080116180014197115781370507757705909/4213632214447170539336951362748416000000000000000000), (385242162549620573391998403608968280341468891273/2106816107223585269668475681374208000000000000000000), (155408259767410286950694177171334941238904205939/898853976247900279144272443211776000000000000000000), (14454114617757329731561047965543024444916888171197/116401589924103086149183281395924992000000000000000000), (2135371564033184029266686669519501241709347141809/58200794962051543074591640697962496000000000000000000)]
    reserve := (36689731/1000000000000) }

theorem mixed_004_175_valid : mixed_004_175.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_175]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_175]
  · intro i; fin_cases i <;> norm_num [mixed_004_175]
  · norm_num [mixed_004_175]
  · norm_num [mixed_004_175, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_175, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_175, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_175, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_175]

def mixed_004_176 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(29/1280), (59/2560)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(7445819/50000000), (14907199/100000000), (8575341/100000000), (3596929/25000000), (3596929/25000000), (16515511/100000000), (16334879/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(13619/2000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1396313/25000000), (1471/100000000), (1086379/25000000), (2116121/50000000), (1/100000000), (2767303/50000000), (196621/100000000)]
    alternative := .zero
    polynomial := [(-12404890530877757860138652491791061171054465847/15730013754111072294412239525827700000000000000), (2549778593267/36775000000), (-11989614535120609511319658166666208124872677965847/7865006877055536147206119762913850000000000000), (2549778593267/36775000000), (-23966824179710341264779177680840625188574301465847/15730013754111072294412239525827700000000000000)]
    bernstein := [(6637563953402140030515371402803449446573563108996834393/42224934149710775659995157690967824269312000000000000000000), (5235839659547670352466842949100947853089257651745035701/28149956099807183773330105127311882846208000000000000000000), (89195934032568429383904868416435389074243242727897215739/506699209796529307919941892291613891231744000000000000000000), (14333935304501148342370890876649424310215118263775103941/112599824399228735093320420509247531384832000000000000000000), (26886535142798058783892149597761192761983432756697379833/675598946395372410559922523055485188308992000000000000000000)]
    reserve := (39796591/1000000000000) }

theorem mixed_004_176_valid : mixed_004_176.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_176]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_176]
  · intro i; fin_cases i <;> norm_num [mixed_004_176]
  · norm_num [mixed_004_176]
  · norm_num [mixed_004_176, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_176, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_176, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_176, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_176]

def mixed_004_177 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(59/2560), (3/128)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(7449293/50000000), (14914691/100000000), (8576949/100000000), (7192991/50000000), (7192991/50000000), (4127649/25000000), (8163607/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(346463/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1396251/25000000), (23/1562500), (27171/625000), (2116037/50000000), (1/100000000), (2766691/50000000), (199861/100000000)]
    alternative := .zero
    polynomial := [(-37029111861779372238180844282561830170310371/45376020798483769764998230587600000000000000), (5191422246941/73600000000), (-34592045978643454315785445216396647325146622871/22688010399241884882499115293800000000000000), (5191422246941/73600000000), (-69147062845425129259332709588510732820122935371/45376020798483769764998230587600000000000000)]
    bernstein := [(312502706122744181721801205941564811231020681803216869/1948885253521035975274610058716088631296000000000000000000), (18432414989261788927083195807904212276274338269195293/97444262676051798763730502935804431564800000000000000000), (2619205697245911431421956018163182809696980046980799/14616639401407769814559575440370664734720000000000000000), (31779756798677834612176129564180991036565298378829/243610656690129496909326257339511078912000000000000000), (522988022700610309198728318008175298579369188421/12180532834506474845466312866975553945600000000000000)]
    reserve := (21468191/500000000000) }

theorem mixed_004_177_valid : mixed_004_177.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_177]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_177]
  · intro i; fin_cases i <;> norm_num [mixed_004_177]
  · norm_num [mixed_004_177]
  · norm_num [mixed_004_177, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_177, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_177, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_177, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_177]

def mixed_004_178 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/128), (61/2560)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(3726383/25000000), (14922191/100000000), (4289279/50000000), (2876849/20000000), (2876849/20000000), (660227/4000000), (3263911/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(704913/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2792379/50000000), (1473/100000000), (869841/20000000), (846381/20000000), (1/100000000), (1383039/25000000), (101549/50000000)]
    alternative := .zero
    polynomial := [(-120579942536981500562586301300233902518741/142873145258957796763405003644000000000000), (3522307944471/49100000000), (-108937349983978159566097150267988343544948741/71436572629478898381702501822000000000000), (3522307944471/49100000000), (-217754120025419337631631714234676453187378741/142873145258957796763405003644000000000000)]
    bernstein := [(6271220764544080159873957192941562754342015291/38352217897742574258939946265858801664000000000000), (147524464952192559472529994913259146362805842181/767044357954851485178798925317176033280000000000000), (51488746015658600612451067031904139588102919963/282347616425098706200784880484850073600000000000000), (40993394901692994175167784106175995748303457133957/306817743181940594071519570126870413312000000000000000), (282726450082547066271592642255708265814267123394619/6136354863638811881430391402537408266240000000000000000)]
    reserve := (9214801/200000000000) }

theorem mixed_004_178_valid : mixed_004_178.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_178]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_178]
  · intro i; fin_cases i <;> norm_num [mixed_004_178]
  · norm_num [mixed_004_178]
  · norm_num [mixed_004_178, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_178, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_178, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_178, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_178]

def mixed_004_179 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(61/2560), (31/1280)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14912477/100000000), (149297/1000000), (8580167/100000000), (2876501/20000000), (1797813/12500000), (8250373/50000000), (163119/1000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(44807/6250000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2792257/50000000), (1473/100000000), (4351053/100000000), (528967/12500000), (1/100000000), (345683/6250000), (51583/25000000)]
    alternative := .zero
    polynomial := [(-26987556962851058509581499206827130596607379/30915271432674050432555982951150000000000000), (53756679719/736500000), (-7864102668474023232278341029435762931803035793/5152545238779008405425997158525000000000000), (53756679719/736500000), (-47157628453881288335160464677407750460221607379/30915271432674050432555982951150000000000000)]
    bernstein := [(221316271679708112386860906607049210696816232988934461/1327800797502981124356826004643228155904000000000000000000), (9986018481958514224057531725331835614388114887098587/51069261442422350936801000178585698304000000000000000000), (2933562131767269664521025623952287106014000394834881/15807152351225965766152690531467001856000000000000000000), (1746760142580316630835180493661302194447739555534467/12767315360605587734200250044646424576000000000000000000), (4085406761816045033917014284884126703187544447079341/82987549843936320272301625290201759744000000000000000000)]
    reserve := (1538411/31250000000) }

theorem mixed_004_179_valid : mixed_004_179.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_179]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_179]
  · intro i; fin_cases i <;> norm_num [mixed_004_179]
  · norm_num [mixed_004_179]
  · norm_num [mixed_004_179, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_179, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_179, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_179, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_179]

def mixed_004_180 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(31/1280), (63/2560)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14919421/100000000), (14937217/100000000), (536361/6250000), (14380761/100000000), (359519/2500000), (8247907/50000000), (16304251/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(364461/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(349017/6250000), (737/50000000), (4352903/100000000), (2115783/50000000), (1/100000000), (5529699/100000000), (209563/100000000)]
    alternative := .zero
    polynomial := [(-573097332175850594800087416121647581851040029/635472167214823971786735694916568750000000000), (5468065511011/73700000000), (-60629664302097765511423160699150087747610417113/39717010450926498236670980932285546875000000), (5468065511011/73700000000), (-969501531501388397587970483770279756379915633779/635472167214823971786735694916568750000000000)]
    bernstein := [(289773216174090261375318370005167617045709148421404941/1705832609816195228263035310164060143616000000000000000000), (678022640793002617794914191439319741096402373487978093/3411665219632390456526070620328120287232000000000000000000), (3864319132172174286050848558547550241703733698003179367/20469991317794342739156423721968721723392000000000000000000), (1910537337015503568588804845640673962458695171197213997/13646660878529561826104282481312481148928000000000000000000), (1430097715835742346347412914750055838113464982509463181/27293321757059123652208564962624962297856000000000000000000)]
    reserve := (52397349/1000000000000) }

theorem mixed_004_180_valid : mixed_004_180.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_180]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_180]
  · intro i; fin_cases i <;> norm_num [mixed_004_180]
  · norm_num [mixed_004_180]
  · norm_num [mixed_004_180, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_180, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_180, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_180, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_180]

def mixed_004_181 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(63/2560), (1/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(3731591/25000000), (14944743/100000000), (4291693/50000000), (14379013/100000000), (14379013/100000000), (8245437/50000000), (16296607/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(740943/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(174501/3125000), (59/4000000), (2177377/50000000), (846279/20000000), (1/100000000), (1382117/25000000), (21279/10000000)]
    alternative := .zero
    polynomial := [(-11915370408550465052422809175476634928123/12795488168295282776422450200000000000000), (11121277703299/147500000000), (-9768303341728114989868861311214082298248123/6397744084147641388211225100000000000000), (11121277703299/147500000000), (-19524691313047679514685299813252687961568123/12795488168295282776422450200000000000000)]
    bernstein := [(95123811798189393631691412396895839069384076011397/549562032191831835958065034891886592000000000000000000), (1734168104363061977615119116129610546860059433019/8586906752997372436844766170185728000000000000000000), (77278437076895810462382601873790789668352137039/402511254046751832977098414227456000000000000000000), (300199132608906860264655155093763912796694651/2096412781493499130089054240768000000000000000000), (1820317061820614349313517570763175924758277/32756449710835923907641472512000000000000000000)]
    reserve := (6946407/125000000000) }

theorem mixed_004_181_valid : mixed_004_181.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_181]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_181]
  · intro i; fin_cases i <;> norm_num [mixed_004_181]
  · norm_num [mixed_004_181]
  · norm_num [mixed_004_181, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_181, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_181, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_181, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_181]

def mixed_004_182 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/40), (13/512)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(7466653/50000000), (7476139/50000000), (1716999/20000000), (7188631/50000000), (7188631/50000000), (16485929/100000000), (2036121/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(752977/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2791897/50000000), (369/25000000), (17018/390625), (4231223/100000000), (1/100000000), (1381809/25000000), (108007/50000000)]
    alternative := .zero
    polynomial := [(-5674859795900037987030217985046536212221461263/5904713639437730993109947717347200000000000000), (5653403232571/73800000000), (-1502885287415478501392764302512125995367065820421/984118939906288498851657952891200000000000000), (5653403232571/73800000000), (-9011636864696970970369555597087709435990173461263/5904713639437730993109947717347200000000000000)]
    bernstein := [(2664900286488276313540723728133398420878077217137/15116066916960591342361466156408832000000000000000000), (3608967888499449846405894610260782272273700916631/17589605139735960834747887891093913600000000000000000), (483484832135237174940572236500557005377472286622169/2476616403674823285532502615066023034880000000000000000), (421982159141275190465291080421378542863578587902703/2881880906094339823165093952076826804224000000000000000), (23856421781028064962139784202068280850340151350369153/405768831578083047101645228452417214034739200000000000000)]
    reserve := (11758627/200000000000) }

theorem mixed_004_182_valid : mixed_004_182.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_182]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_182]
  · intro i; fin_cases i <;> norm_num [mixed_004_182]
  · norm_num [mixed_004_182]
  · norm_num [mixed_004_182, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_182, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_182, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_182, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_182]

def mixed_004_183 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(13/512), (33/1280)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14940247/100000000), (14959821/100000000), (1717321/20000000), (3593877/25000000), (14375507/100000000), (8240489/50000000), (8140667/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(765021/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2791779/50000000), (369/25000000), (4358463/100000000), (4231051/100000000), (1/100000000), (2763001/50000000), (43847/20000000)]
    alternative := .zero
    polynomial := [(-12684790873208563337397319343122168547813863531/12786080884284661891415523173556450000000000000), (1276959968801/16400000000), (-9771599023683594260336370854213591003283256251031/6393040442142330945707761586778225000000000000), (1276959968801/16400000000), (-19530513256493979957335344389084059838018698638531/12786080884284661891415523173556450000000000000)]
    bernstein := [(157738658966319112241851441574099057628162077504184461/878652787872214130848754802834481356157747200000000000000), (457874797032408139884336702499689418529503141301276833/2196631969680535327121887007086203390394368000000000000000), (3270140031157464712839534580893967936454900128123692431/16474739772604014953414152553146525427957760000000000000000), (2054848371886993322601548277514332105587862308665885049/13728949810503345794511793794288771189964800000000000000000), (2127240557398214205471275150252041751932496787766626749/34322374526258364486279484485721927974912000000000000000000)]
    reserve := (12395649/200000000000) }

theorem mixed_004_183_valid : mixed_004_183.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_183]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_183]
  · intro i; fin_cases i <;> norm_num [mixed_004_183]
  · norm_num [mixed_004_183]
  · norm_num [mixed_004_183, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_183, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_183, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_183, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_183]

def mixed_004_184 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(33/1280), (67/2560)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14947187/100000000), (3741843/25000000), (1073527/12500000), (11499/80000), (11499/80000), (823801/5000000), (3254741/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(777077/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1395831/25000000), (1477/100000000), (4360321/100000000), (4230879/100000000), (1/100000000), (2762383/50000000), (222453/100000000)]
    alternative := .zero
    polynomial := [(-271053874752367816707606793870645896553203097/264981757796482201446491613528435000000000000), (834205218301/10550000000), (-202550949869826720138608367233427775336307803097/132490878898241100723245806764217500000000000), (834205218301/10550000000), (-14993735032033373054092930654554996473187496411/9814139177647488942462652352905000000000000)]
    bernstein := [(130014744166938656998387506254435895977237420092668263/711304989857802549411728358776812181913600000000000000000), (301181712867001881931805204216004745104842497647121237/1422609979715605098823456717553624363827200000000000000000), (1722149117902894257559885194701133196523909837100392989/8535659878293630592940740305321746182963200000000000000000), (290076326709387047532022596087820501876643681353791679/1896813306287473465097942290071499151769600000000000000000), (742217398044330925231954722830676307582426082850640663/11380879837724840790587653740428994910617600000000000000000)]
    reserve := (6521617/100000000000) }

theorem mixed_004_184_valid : mixed_004_184.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_184]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_184]
  · intro i; fin_cases i <;> norm_num [mixed_004_184]
  · norm_num [mixed_004_184]
  · norm_num [mixed_004_184, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_184, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_184, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_184, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_184]

def mixed_004_185 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(67/2560), (17/640)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(119633/800000), (14974933/100000000), (4294913/50000000), (14371989/100000000), (14371989/100000000), (16471057/100000000), (16266081/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(157829/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1395773/25000000), (739/50000000), (218109/5000000), (846141/20000000), (1/100000000), (690441/12500000), (56417/25000000)]
    alternative := .zero
    polynomial := [(-86857561039389532865115438644850808309385183/82389071686133016367099089591900000000000000), (11865476037721/147800000000), (-62991232676196918399650682252691085591630510183/41194535843066508183549544795950000000000000), (11865476037721/147800000000), (-125895607791354447266436249066737320374951635183/82389071686133016367099089591900000000000000)]
    bernstein := [(22698927123333176647730021022098538491833982509152533/122020127048186511035352869030546374656000000000000000000), (2185844725341146312455193622002470108314789219216061/10168343920682209252946072419212197888000000000000000000), (136026503835702648577538067367165142416206401778784171/663484440824514153754731225353595912192000000000000000000), (2878473191684651075709155055303682045874148602733569/18430123356236504270964756259822108672000000000000000000), (946273959663800876806345986227636569087585919570257/13822592517177378203223567194866581504000000000000000000)]
    reserve := (136917/2000000000) }

theorem mixed_004_185_valid : mixed_004_185.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_185]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_185]
  · intro i; fin_cases i <;> norm_num [mixed_004_185]
  · norm_num [mixed_004_185]
  · norm_num [mixed_004_185, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_185, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_185, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_185, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_185]

def mixed_004_186 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(17/640), (69/2560)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14961063/100000000), (7491251/50000000), (8591437/100000000), (898139/6250000), (898139/6250000), (2058261/12500000), (8129231/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(100153/12500000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2791431/50000000), (739/50000000), (2182021/50000000), (1057633/25000000), (1/100000000), (5522289/100000000), (2861/1250000)]
    alternative := .zero
    polynomial := [(-340588684007080073232697041749169068334525151/313394233958195454841761590939887500000000000), (301310004903/3695000000), (-239820986993315662831847645813211198787959600151/156697116979097727420880795469943750000000000), (301310004903/3695000000), (-479301385302624245590462594584673228507584675151/313394233958195454841761590939887500000000000)]
    bernstein := [(9953162235565960094717677990843896492151304121484529/52578827562711801160984800317021356032000000000000000000), (45908792041368393002141903113642200543694032805478053/210315310250847204643939201268085424128000000000000000000), (525830062374007789611390109411795829233599506965010363/2523783723010166455727270415217025089536000000000000000000), (536696555396959320428027840811273698130283970832627197/3365044964013555274303027220289366786048000000000000000000), (965223641367137380960317992776683887131069345959370529/13460179856054221097212108881157467144192000000000000000000)]
    reserve := (17927391/250000000000) }

theorem mixed_004_186_valid : mixed_004_186.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_186]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_186]
  · intro i; fin_cases i <;> norm_num [mixed_004_186]
  · norm_num [mixed_004_186]
  · norm_num [mixed_004_186, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_186, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_186, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_186, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_186]

def mixed_004_187 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(69/2560), (7/256)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14967999/100000000), (14990079/100000000), (8593049/100000000), (1796057/12500000), (1796057/12500000), (16461113/100000000), (507839/3125000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(162663/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5582633/100000000), (1479/100000000), (873181/20000000), (4230357/100000000), (1/100000000), (690131/12500000), (232089/100000000)]
    alternative := .zero
    polynomial := [(-141591490436982057967655442541453626883724743/126524561310214702120459245736100000000000000), (4079908703423/49300000000), (-3195809432871200915006068766869168127147310416519/2087655261618542584987577554645650000000000000), (4079908703423/49300000000), (-6386946346557981422099204904134468284607457916519/4175310523237085169975155109291300000000000000)]
    bernstein := [(677159541510438253239600645074291044352240719016640851/3516239636852535070472527907241850830848000000000000000000), (45672802201605002738072131778499938440364689154121349/206124392505148607579424049734867117670400000000000000000), (1138628891960002191554777338512212231693861633011268323/5379846644384378657822967698080031771197440000000000000000), (5838358502015715131859217679494961411667420198328511/35865644295895857718819784653866878474649600000000000000), (4137723171052485040467338301120867775573118259493/55177914301378242644338130236718274576384000000000000)]
    reserve := (18747189/250000000000) }

theorem mixed_004_187_valid : mixed_004_187.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_187]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_187]
  · intro i; fin_cases i <;> norm_num [mixed_004_187]
  · norm_num [mixed_004_187]
  · norm_num [mixed_004_187, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_187, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_187, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_187, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_187]

def mixed_004_188 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(7/256), (71/2560)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(2994987/20000000), (7498833/50000000), (429733/5000000), (3591671/25000000), (3591671/25000000), (4114033/25000000), (16243239/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(825417/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5582407/100000000), (37/2500000), (4367771/100000000), (2115091/50000000), (1/100000000), (2759903/50000000), (117647/50000000)]
    alternative := .zero
    polynomial := [(-2230191904338070528490815418143098963839717909/1936140349560065742891452342619559375000000000), (6213704232081/74000000000), (-5929072732044960419371257511427759783471257449761/3872280699120131485782904685239118750000000000), (6213704232081/74000000000), (-5924612348236284278314275880591473585543578013943/3872280699120131485782904685239118750000000000)]
    bernstein := [(130309549730792572535244801273066518249031579608273/665252758546119228266298583159487558844416000000000000), (7480258346028014990677454940823206563045197219821333/33262637927305961413314929157974377942220800000000000000), (1072475114614157927498810882375200186672121124765334331/4989395689095894211997239373696156691333120000000000000000), (2762081707775446251246926339040432478155252766795471209/16631318963652980706657464578987188971110400000000000000000), (13016018951436072993568497270498882898958349669532378217/166313189636529807066574645789871889711104000000000000000000)]
    reserve := (4891381/62500000000) }

theorem mixed_004_188_valid : mixed_004_188.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_188]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_188]
  · intro i; fin_cases i <;> norm_num [mixed_004_188]
  · norm_num [mixed_004_188]
  · norm_num [mixed_004_188, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_188, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_188, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_188, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_188]

def mixed_004_189 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(71/2560), (9/320)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14981869/100000000), (15005261/100000000), (537267/6250000), (14364909/100000000), (14364909/100000000), (3290229/20000000), (3247127/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(837531/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5582183/100000000), (37/2500000), (4369639/100000000), (2115003/50000000), (1/100000000), (5518561/100000000), (7453/3125000)]
    alternative := .zero
    polynomial := [(-2415254042559040604150202480563942368625689/2036549295719966631196936519220000000000000), (12615428730191/148000000000), (-195067854182289516349154232640193097526264383/127284330982497914449808532451250000000000), (12615428730191/148000000000), (-3118670412874073220982317519762525618051604439/2036549295719966631196936519220000000000000)]
    bernstein := [(17422684659626230688925707188673714550377297961615241/87469126218090894552021356854379754291200000000000000000), (2495525162452383568612763329282598747295084851811239/10933640777261361819002669606797469286400000000000000000), (298386173839413459900308396701157795655394398845481/1366705097157670227375333700849683660800000000000000000), (28945538696540954056682588223216901023810092238599/170838137144708778421916712606210457600000000000000000), (47074864840851562097346222510791974804894814933/577155868732124251425394299345305600000000000000000)]
    reserve := (81563521/1000000000000) }

theorem mixed_004_189_valid : mixed_004_189.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_189]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_189]
  · intro i; fin_cases i <;> norm_num [mixed_004_189]
  · norm_num [mixed_004_189]
  · norm_num [mixed_004_189, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_189, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_189, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_189, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_189]

def mixed_004_190 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(9/320), (73/2560)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(7494401/50000000), (3002573/20000000), (2149471/25000000), (14363131/100000000), (14363131/100000000), (2055769/12500000), (4057009/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(849657/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(139549/2500000), (1481/100000000), (1092877/25000000), (422983/10000000), (1/100000000), (1379329/25000000), (48339/20000000)]
    alternative := .zero
    polynomial := [(-24280596964527598643065619532981777846059939/19906345485836874077924673969215625000000000), (12803853279937/148100000000), (-15257153611765779824668536818295888897856066189/9953172742918437038962336984607812500000000), (12803853279937/148100000000), (-3387780736285225783410445335228755113096230271/2211816165092986008658297107690625000000000)]
    bernstein := [(42268910284417041601381668180733008994229104004521/208733161241568860731339429319442432000000000000000000), (7296208272648062091392610730232016050105357791429/31506892262878318600956894991613952000000000000000000), (8883616121306507366752971280146000592039736974171067/40076766958381221260417170429332946944000000000000000000), (116127414604990135874988583458880338231969476704087/672147034941404130153747093154430976000000000000000000), (72579565714269291069389764320108613386651893020777001/854971028445466053555566302492436201472000000000000000000)]
    reserve := (84891257/1000000000000) }

theorem mixed_004_190_valid : mixed_004_190.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_190]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_190]
  · intro i; fin_cases i <;> norm_num [mixed_004_190]
  · norm_num [mixed_004_190]
  · norm_num [mixed_004_190, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_190, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_190, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_190, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_190]

def mixed_004_191 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(73/2560), (37/1280)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(7497867/50000000), (15020477/100000000), (8599497/100000000), (14361349/100000000), (14361349/100000000), (16441153/100000000), (8110221/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(430897/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(279087/5000000), (741/50000000), (218669/5000000), (4229653/100000000), (1/100000000), (1379017/25000000), (244891/100000000)]
    alternative := .zero
    polynomial := [(-142108364035208226607549659159663945656089097/113322817210577195109498048624900000000000000), (6496317172913/74100000000), (-86876484757045340881980919681201134678588589097/56661408605288597554749024312450000000000000), (6496317172913/74100000000), (-173610861150055473537354289703242605411521089097/113322817210577195109498048624900000000000000)]
    bernstein := [(77067120375476456563754135618384566883392356319886771/374398302930780767906696352169048670208000000000000000000), (190571786604889524654957356105828641790804572742673129/811196323016691663797842096366272118784000000000000000000), (821405586348999828989617536804840214231042801835788909/3650383453575112487090289433648224534528000000000000000000), (35716518173933766773940002116012987934334494565585969/202799080754172915949460524091568029696000000000000000000), (688126913350859751147434543021031182853161483580897/7799964644391265998056174003521847296000000000000000000)]
    reserve := (88221799/1000000000000) }

theorem mixed_004_191_valid : mixed_004_191.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_191]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_191]
  · intro i; fin_cases i <;> norm_num [mixed_004_191]
  · norm_num [mixed_004_191]
  · norm_num [mixed_004_191, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_191, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_191, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_191, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_191]

def mixed_004_192 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(37/1280), (15/512)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(3000533/20000000), (7514049/50000000), (8601109/100000000), (14359563/100000000), (14359563/100000000), (4109037/25000000), (16212853/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(436971/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5581521/100000000), (1483/100000000), (2187627/50000000), (169179/4000000), (1/100000000), (5514819/100000000), (62021/25000000)]
    alternative := .zero
    polynomial := [(-78147573270895421695232871886354963295583221/60637282783534913619017330127660937500000000), (6590886672157/74150000000), (-92994906336583893117823827613644197831995744567/60637282783534913619017330127660937500000000), (6590886672157/74150000000), (-46458379381656498848064297370878921434350080673/30318641391767456809508665063830468750000000)]
    bernstein := [(17026046933394532616484786691294615993935191683848047/81385983272995719146207636423606009856000000000000000000), (119345112562249670113898445525053160841830113737133/500836820141512117822816224145267752960000000000000000), (8921732127493890953074721661700610621344975867306997/39065271971037945190179665483330884730880000000000000000), (14381315231579635410979287959549038968360905845333/80133891222641938851650595863242840473600000000000000), (190738300493764442820796453385771287436179820895647/2083481171788690410142915492444313852313600000000000000)]
    reserve := (91547887/1000000000000) }

theorem mixed_004_192_valid : mixed_004_192.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_192]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_192]
  · intro i; fin_cases i <;> norm_num [mixed_004_192]
  · norm_num [mixed_004_192]
  · norm_num [mixed_004_192, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_192, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_192, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_192, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_192]

def mixed_004_193 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(15/512), (19/640)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(3001919/20000000), (939733/6250000), (8602723/100000000), (7178887/50000000), (7178887/50000000), (16431137/100000000), (16205269/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(443051/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(697663/12500000), (1483/100000000), (4377129/100000000), (4229297/100000000), (1/100000000), (172299/3125000), (125637/50000000)]
    alternative := .zero
    polynomial := [(-12207266940341367185400216497856608329654282211/9213659814272287271603929643587800000000000000), (1337125348011/14830000000), (-2357204452181462795275416396053644137074493260737/1535609969045381211933988273931300000000000000), (1337125348011/14830000000), (-14131019446148435404467098159824008214117305282211/9213659814272287271603929643587800000000000000)]
    bernstein := [(134590022427186729309109281514292970840302945130752029/633157881260302525930495156548712593673420800000000000000), (38260011475068581586670651727649020534838974011374613/158289470315075631482623789137178148418355200000000000000), (76444484960751075095878048194482308617936547861978839/329769729823074232255466227369121142538240000000000000000), (45230184785875683654685493812449414562013902108148797/247327297367305674191599670526840856903680000000000000000), (48898733743322003385082064143701262886638039291179023/515265202848553487899165980264251785216000000000000000000)]
    reserve := (2965629/31250000000) }

theorem mixed_004_193_valid : mixed_004_193.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_193]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_193]
  · intro i; fin_cases i <;> norm_num [mixed_004_193]
  · norm_num [mixed_004_193]
  · norm_num [mixed_004_193, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_193, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_193, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_193, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_193]

def mixed_004_194 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(19/640), (77/2560)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(3754131/25000000), (15043367/100000000), (537771/6250000), (7177991/50000000), (7177991/50000000), (16426121/100000000), (16197689/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(449137/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(558109/10000000), (371/25000000), (4379007/100000000), (2114559/50000000), (1/100000000), (1102463/20000000), (254461/100000000)]
    alternative := .zero
    polynomial := [(-399921553745233439754833905536445385552750687/293915537413386863974429960334700000000000000), (1356114018951/14840000000), (-32234312696625162126973125584769408600854107241/20993966958099061712459282881050000000000000), (1356114018951/14840000000), (-450880456199007036337868924281235275026404750687/293915537413386863974429960334700000000000000)]
    bernstein := [(10648559109039801967813748734219473789068752644465073/49310844569404727084616299214066941952000000000000000000), (5371635158937224618520064746487597312030740382932151/21915930919735434259829466317363085312000000000000000000), (556721734730204876382837044460714030926076662352631891/2366920539331426900061582362275213213696000000000000000000), (65316007100049469559780039801192269462365426037704439/350654894715766948157271461077809364992000000000000000000), (1240625334437287590660413470707152448628118293033085233/12623576209767610133661772598801137139712000000000000000000)]
    reserve := (24569609/250000000000) }

theorem mixed_004_194_valid : mixed_004_194.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_194]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_194]
  · intro i; fin_cases i <;> norm_num [mixed_004_194]
  · norm_num [mixed_004_194]
  · norm_num [mixed_004_194, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_194, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_194, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_194, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_194]

def mixed_004_195 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(77/2560), (39/1280)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(3755863/25000000), (7525507/50000000), (8605949/100000000), (7177093/50000000), (7177093/50000000), (8210549/50000000), (3238023/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(910457/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5580877/100000000), (297/20000000), (4380887/100000000), (2114469/50000000), (1/100000000), (5511061/100000000), (64411/25000000)]
    alternative := .zero
    polynomial := [(-6042499038756703828946578446055785231527460881/4325606295174660356319942802345950000000000000), (312531493067/3375000000), (-1107206761221435145862333955474102264535629878627/720934382529110059386657133724325000000000000), (312531493067/3375000000), (-6637198068289854171345057154398557801982251810881/4325606295174660356319942802345950000000000000)]
    bernstein := [(40752142498793989986727607740776633520287988949427468079/185783375731468888383018612486664473280512000000000000000000), (7695017624869551591200567914860426335973111867721661551/30963895955244814730503102081110745546752000000000000000000), (30035234392146366805191115367157519817883607173070359/125869495753027702156516675126466445312000000000000000000), (1468232851390517327687469036890346611783276552331152999/7740973988811203682625775520277686386688000000000000000000), (1180411988594913683966022545046420210532888612045011679/11611460983216805523938663280416529580032000000000000000000)]
    reserve := (101659213/1000000000000) }

theorem mixed_004_195_valid : mixed_004_195.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_195]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_195]
  · intro i; fin_cases i <;> norm_num [mixed_004_195]
  · norm_num [mixed_004_195]
  · norm_num [mixed_004_195, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_195, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_195, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_195, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_195]

def mixed_004_196 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(39/1280), (79/2560)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(7515189/50000000), (15058671/100000000), (8607563/100000000), (14352387/100000000), (14352387/100000000), (16416069/100000000), (3236509/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(230663/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2790333/50000000), (743/50000000), (4382769/100000000), (2114379/50000000), (1/100000000), (1101961/20000000), (10433/4000000)]
    alternative := .zero
    polynomial := [(-55848535035130751396658931869213325964669579/38955487171812531243569497679100000000000000), (108921933119/1160937500), (-29921419903984653275232890825555929279362869579/19477743585906265621784748839550000000000000), (108921933119/1160937500), (-59786991272934175799069122719242645232761069579/38955487171812531243569497679100000000000000)]
    bernstein := [(23293365545266505913776180188507059060458407475237461/104570339626676471708818251771801501696000000000000000000), (52688670871409180390414381587666669445200964573007821/209140679253352943417636503543603003392000000000000000000), (43388754312581515591858620165231602768027054836360249/179263439360016808643688431608802574336000000000000000000), (161524272155738607632220460753437035265858340393135741/836562717013411773670546014174412013568000000000000000000), (175767495115182392852346485494624285153802766280293301/1673125434026823547341092028348824027136000000000000000000)]
    reserve := (105053387/1000000000000) }

theorem mixed_004_196_valid : mixed_004_196.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_196]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_196]
  · intro i; fin_cases i <;> norm_num [mixed_004_196]
  · norm_num [mixed_004_196]
  · norm_num [mixed_004_196, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_196, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_196, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_196, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_196]

def mixed_004_197 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(79/2560), (1/32)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(1879663/12500000), (470823/3125000), (4304589/50000000), (1793823/12500000), (1793823/12500000), (3282207/20000000), (808749/5000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(934859/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5580457/100000000), (743/50000000), (4384653/100000000), (4228577/100000000), (1/100000000), (1377137/25000000), (132001/50000000)]
    alternative := .zero
    polynomial := [(-411377871826599405926488641805430856213210732689/279493952881627945739547295538906940000000000000), (883310740449/9287500000), (-214876167409398857378102189625296030332680644532689/139746976440813972869773647769453470000000000000), (883310740449/9287500000), (-429340956946971115350277890608786629809148078332689/279493952881627945739547295538906940000000000000)]
    bernstein := [(2715104158443491961006490322675250033261110241777524409391/12004173870563569861910181681848520028874342400000000000000000), (12775041066325827305445240807035984598936011912358441483/50017391127348207757959090341035500120309760000000000000000), (1381649931867814957458463678564716929457984673847316397/5626956501826673372770397663366493763534848000000000000000), (61448365863688517501931311787010128858055958290083/312608694545926298487244314631471875751936000000000000), (50870496275112114768677340103819674549454013791/468913041818889447730866471947207813627904000000000)]
    reserve := (108485991/1000000000000) }

theorem mixed_004_197_valid : mixed_004_197.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_197]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_197]
  · intro i; fin_cases i <;> norm_num [mixed_004_197]
  · norm_num [mixed_004_197]
  · norm_num [mixed_004_197, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_197, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_197, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_197, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_197]

def mixed_004_198 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/32), (81/2560)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(15044229/100000000), (1507401/10000000), (1076349/12500000), (14348777/100000000), (14348777/100000000), (3281199/20000000), (808371/5000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(947077/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(22321/400000), (1487/100000000), (4386539/100000000), (1057099/25000000), (1/100000000), (5507289/100000000), (33397/12500000)]
    alternative := .zero
    polynomial := [(-65744307821895684664640832854697766568538443/43550609751856136897346479094540000000000000), (286486601517/2974000000), (-33490631969587763681647222272762671082276288443/21775304875928068448673239547270000000000000), (286486601517/2974000000), (-9559359947336233096947114816095806342569148349/6221515678836590985335211299220000000000000)]
    bernstein := [(16777881927426016443359643850167006119057317/73065798673859680965235170660858200064000000000), (37829008902457015145756727350770845033403297837/146131597347719361930470341321716400128000000000000), (2763541036538040884203121153610865497474408336241/11098602330206533817504076556079726592000000000000000), (4676543940978059222498624667058136831200249739244677/23381055575635097908875254611474624020480000000000000000), (209332776513885532252469662092684791329695343021758997/1870484446050807832710020368917969921638400000000000000000)]
    reserve := (27978417/250000000000) }

theorem mixed_004_198_valid : mixed_004_198.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_198]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_198]
  · intro i; fin_cases i <;> norm_num [mixed_004_198]
  · norm_num [mixed_004_198]
  · norm_num [mixed_004_198, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_198, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_198, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_198, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_198]

def mixed_004_199 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(81/2560), (41/1280)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(940697/6250000), (3770423/25000000), (8612407/100000000), (1793371/12500000), (1793371/12500000), (4100237/25000000), (3231973/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(959307/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1395011/25000000), (93/6250000), (4388427/100000000), (2114107/50000000), (1/100000000), (1376507/25000000), (270347/100000000)]
    alternative := .zero
    polynomial := [(-67771446957419321666381474392508603682983813/43784537694611158314659520908100000000000000), (1209672038807/12400000000), (-33679409190382837626159634297703960834166983813/21892268847305579157329760454050000000000000), (1209672038807/12400000000), (-2170678933348653417117835068419852034343580123/1412404441761650268214823255100000000000000)]
    bernstein := [(438323630125938266637679797398836609720677109652423227/1880531574688341603981411196753177214976000000000000000000), (246671419788830144285327236504186827250556380328418947/940265787344170801990705598376588607488000000000000000000), (356092211708951289452812121750467879638497653218122401/1410398681016256202986058397564882911232000000000000000000), (47832655165977252209164249576193346510011033618088787/235066446836042700497676399594147151872000000000000000000), (1232698480302941527883188502364857605004163172487537/10684838492547395477167109072461234176000000000000000000)]
    reserve := (115368939/1000000000000) }

theorem mixed_004_199_valid : mixed_004_199.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_199]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_199]
  · intro i; fin_cases i <;> norm_num [mixed_004_199]
  · norm_num [mixed_004_199]
  · norm_num [mixed_004_199, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_199, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_199, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_199, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_199]

def mixed_004_200 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(41/1280), (83/2560)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(7529037/50000000), (1886173/12500000), (4307011/50000000), (7172577/50000000), (7172577/50000000), (2049487/12500000), (3230463/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(971549/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5579841/100000000), (93/6250000), (4390317/100000000), (4228031/100000000), (1/100000000), (1100953/20000000), (54703/20000000)]
    alternative := .zero
    polynomial := [(-10233541803415466122667318204027630599149848521/6445791132400657275725651746220100000000000000), (1838518153157/18600000000), (-4962789172609447330067930490573444733201436348521/3222895566200328637862825873110050000000000000), (1838518153157/18600000000), (-9915344803415479194013193662942861835803722848521/6445791132400657275725651746220100000000000000)]
    bernstein := [(4092933400011816892968744782976749563233455623491573719/17302788819067268105091330573937888198656000000000000000000), (1022258499858729481060638768949103051991348871952352133/3845064182014948467798073460875086266368000000000000000000), (7593976508280526535409234428810772380479174629979035419/29661923689829602465870852412464951197696000000000000000000), (3183890853913544073733419499735221281080980374665362877/15380256728059793871192293843500345065472000000000000000000), (32900960661845904168373930884052701949908157039769529959/276844621105076289681461289183006211178496000000000000000000)]
    reserve := (59421347/500000000000) }

theorem mixed_004_200_valid : mixed_004_200.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_200]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_200]
  · intro i; fin_cases i <;> norm_num [mixed_004_200]
  · norm_num [mixed_004_200]
  · norm_num [mixed_004_200, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_200, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_200, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_200, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_200]

def mixed_004_201 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(83/2560), (21/640)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(3766249/25000000), (3019417/20000000), (8615637/100000000), (7171669/50000000), (7171669/50000000), (8195419/50000000), (1614477/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(491901/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(139491/2500000), (1489/100000000), (4392209/100000000), (4227847/100000000), (1/100000000), (5503501/100000000), (276679/100000000)]
    alternative := .zero
    polynomial := [(-36748424759876868740229646173429370259574311629/22588377882271163257494352254794550000000000000), (1490062154223/14890000000), (-17396095935359007666363733556310223434986844311629/11294188941135581628747176127397275000000000000), (1490062154223/14890000000), (-34755443445958138463987237466447017499714114311629/22588377882271163257494352254794550000000000000)]
    bernstein := [(17913697339407714582691010043184265706415014628042018607/74627957133880295688319284491574193422336000000000000000000), (65332302763792275433608450755953297606359100740005558917/242540860685110960987037674597616128622592000000000000000000), (47208510959852762822975467732070013016954593874282777337/181905645513833220740278255948212096466944000000000000000000), (3191018274844550766498701819414666053428863156248689173/15158803792819435061689854662351008038912000000000000000000), (463543248819723661301040296447398180494433148375171651/3789700948204858765422463665587752009728000000000000000000)]
    reserve := (122316577/1000000000000) }

theorem mixed_004_201_valid : mixed_004_201.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_201]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_201]
  · intro i; fin_cases i <;> norm_num [mixed_004_201]
  · norm_num [mixed_004_201]
  · norm_num [mixed_004_201, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_201, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_201, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_201, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_201]

def mixed_004_202 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(21/640), (17/512)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(3767979/25000000), (7552397/50000000), (8617253/100000000), (14341517/100000000), (14341517/100000000), (8192887/50000000), (16137229/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(996067/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(69743/1250000), (149/10000000), (549263/12500000), (4227663/100000000), (1/100000000), (1100447/20000000), (279841/100000000)]
    alternative := .zero
    polynomial := [(-4895096657581059215991283654289427801008503/2937159643960481105917217309700000000000000), (7546737893809/74500000000), (-2262625484283092656741191093518170688307608503/1468579821980240552958608654850000000000000), (7546737893809/74500000000), (-4520355871908604254266390903382051948814208503/2937159643960481105917217309700000000000000)]
    bernstein := [(120011805051033855331957785458030429077960680646457/492773617732080869778920329237757952000000000000000000), (107576469706112703953795765356305136789788662046949/394218894185664695823136263390206361600000000000000000), (248874243796894880587264581159299514976524783917027/946125346045595269975527032136495267840000000000000000), (53998238806333119333243825650223183020968963419437/252300092278825405326807208569732071424000000000000000), (25395099496886490214318589896689017481020326505033/201840073823060324261445766855785657139200000000000000)]
    reserve := (62908963/500000000000) }

theorem mixed_004_202_valid : mixed_004_202.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_202]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_202]
  · intro i; fin_cases i <;> norm_num [mixed_004_202]
  · norm_num [mixed_004_202]
  · norm_num [mixed_004_202, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_202, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_202, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_202, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_202]

def mixed_004_203 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(17/512), (43/1280)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(3015767/20000000), (236133/1562500), (8618869/100000000), (7169847/50000000), (14339693/100000000), (511897/3125000), (16129693/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(126043/12500000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2789621/50000000), (1491/100000000), (1099/25000), (4227479/100000000), (1/100000000), (687621/12500000), (282999/100000000)]
    alternative := .zero
    polynomial := [(-2910852364781847372033510806032012750989187/1705404628040960093951946217800000000000000), (2547784924109/24850000000), (-9198780161716426951340760068966174103560924309/5968916198143360328831811762300000000000000), (2547784924109/24850000000), (-6125728118959793657025761854096708039288308103/3979277465428906885887874508200000000000000)]
    bernstein := [(202671282889429177917176362335757249729875076601899/820361595634892433020045996912212023705600000000000000), (566893220115058830252040573894680541714030793442473/2050903989087231082550114992280530059264000000000000000), (4100472192136555594628925342679533902911152993492889/15381779918154233119125862442103975444480000000000000000), (2788651929932133316349751691877080230165594699626369/12818149931795194265938218701753312870400000000000000000), (4144595018363215554037473657623297161687456621437691/32045374829487985664845546754383282176000000000000000000)]
    reserve := (129335201/1000000000000) }

theorem mixed_004_203_valid : mixed_004_203.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_203]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_203]
  · intro i; fin_cases i <;> norm_num [mixed_004_203]
  · norm_num [mixed_004_203]
  · norm_num [mixed_004_203, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_203, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_203, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_203, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_203]

def mixed_004_204 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(43/1280), (87/2560)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(15085753/100000000), (15120239/100000000), (1724097/20000000), (7168933/50000000), (7168933/50000000), (4093907/25000000), (8061081/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(127579/12500000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5579047/100000000), (1491/100000000), (2198949/50000000), (4227293/100000000), (1/100000000), (5499699/100000000), (143077/50000000)]
    alternative := .zero
    polynomial := [(-1029824897506717239478472581884930715999130063/588897241395765832620194338882725000000000000), (3870069014533/37275000000), (-151402601002363222853997557353935917413432585021/98149540232627638770032389813787500000000000), (3870069014533/37275000000), (-129626540159524659983500981648818653394942340009/84128177342252261802884905554675000000000000)]
    bernstein := [(56592939458973702162638122590219899081841547986621991/225829856473163539640887917380861165568000000000000000000), (295096213560089398712331521095416617832426027202871111/1053872663541429851657476947777352105984000000000000000000), (244071301649744609216741974279925455642775073806270671/903319425892654158563551669523444662272000000000000000000), (932238712907401124069502815218154166076444322535498991/4215490654165719406629907791109408423936000000000000000000), (3360576807598279146751152296756718510864522813776086657/25292943924994316439779446746656450543616000000000000000000)]
    reserve := (66433089/500000000000) }

theorem mixed_004_204_valid : mixed_004_204.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_204]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_204]
  · intro i; fin_cases i <;> norm_num [mixed_004_204]
  · norm_num [mixed_004_204]
  · norm_num [mixed_004_204, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_204, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_204, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_204, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_204]

def mixed_004_205 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(87/2560), (11/320)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(1509267/10000000), (1890997/12500000), (4311051/50000000), (3584009/25000000), (2867207/20000000), (8185273/50000000), (4028659/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(258233/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5578853/100000000), (373/25000000), (4399799/100000000), (1056777/25000000), (1/100000000), (1374607/25000000), (144653/50000000)]
    alternative := .zero
    polynomial := [(-1851446685266464182835853854869716066567688447/1034339216749271737237828212404450000000000000), (122455129527/1165625000), (-797994676847308482671783951832447816455293688447/517169608374635868618914106202225000000000000), (122455129527/1165625000), (-1594137907009350501160732049810025916844019688447/1034339216749271737237828212404450000000000000)]
    bernstein := [(11289868718653992750124031564002670771255541155412019233/44424531089083775432535775463432542748672000000000000000000), (121126177021021466069350279487300009147244712521596673/427158952779651686851305533302235987968000000000000000000), (570054599825022172298077874195229622857263184400756891/2082399894800801973400114474848400441344000000000000000000), (1499688511287158004468255136352790409907045666654057/6674358637182057607051648957847437312000000000000000000), (87019437541065699422450028654201852188761469371169/637990163848284918321113503323652096000000000000000000)]
    reserve := (27279241/200000000000) }

theorem mixed_004_205_valid : mixed_004_205.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_205]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_205]
  · intro i; fin_cases i <;> norm_num [mixed_004_205]
  · norm_num [mixed_004_205]
  · norm_num [mixed_004_205, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_205, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_205, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_205, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_205]

def mixed_004_206 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(11/320), (89/2560)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(7549793/50000000), (15135721/100000000), (8623719/100000000), (14334201/100000000), (14334201/100000000), (8182729/50000000), (8053557/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(261311/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5578661/100000000), (1493/100000000), (2200851/50000000), (4226921/100000000), (1/100000000), (1099431/20000000), (58491/20000000)]
    alternative := .zero
    polynomial := [(-5633862649625769098598668975970138335500189087/3075718335591100821676056230565150000000000000), (247947146927/2332812500), (-2373595170034429295458937469558465070265191489087/1537859167795550410838028115282575000000000000), (247947146927/2332812500), (-4741556477419232821819276270140960002194882789087/3075718335591100821676056230565150000000000000)]
    bernstein := [(8311529737731045499136207991935039785622399896727633/32251244294607741351897923380210827264000000000000000000), (2744044224942050666027336133440828822867157134590721/9555924235439330770932718038580985856000000000000000000), (1717416350878570146679933367392205944026525547642921499/6192238904564686339564401289000478834688000000000000000000), (139617880229027945832907966823274865989810081568849721/611579151068117169339693954469183094784000000000000000000), (18491194520515960269553861389609000866193609119641541633/132101096630713308577373894165343548473344000000000000000000)]
    reserve := (43743/312500000) }

theorem mixed_004_206_valid : mixed_004_206.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_206]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_206]
  · intro i; fin_cases i <;> norm_num [mixed_004_206]
  · norm_num [mixed_004_206]
  · norm_num [mixed_004_206, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_206, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_206, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_206, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_206]

def mixed_004_207 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(89/2560), (9/256)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(15106501/100000000), (605739/4000000), (1078167/12500000), (14332363/100000000), (14332363/100000000), (3272073/20000000), (16099597/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(33049/3125000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5578471/100000000), (747/50000000), (2201803/50000000), (2113367/50000000), (1/100000000), (5495881/100000000), (295601/100000000)]
    alternative := .zero
    polynomial := [(-1180655612091232468469794692117660528666676259201/630031665141365374560742220786009940000000000000), (1338613347053/12450000000), (-486347522722260427745872668515721182591930441009201/315015832570682687280371110393004970000000000000), (1338613347053/12450000000), (-971514389832429623023275542339324704655194205759201/630031665141365374560742220786009940000000000000)]
    bernstein := [(7070487080997403480272896590047806895268971096152192759359/27059653972265875005251782037623241066309222400000000000000000), (786780970638617181140813216682604497840543125162681563919/2705965397226587500525178203762324106630922240000000000000000), (228081347554709839264878341944825096205235706435228959901/811789619167976250157553461128697231989276672000000000000000), (6275149606427125121249819639833720309799423360039033263/27059653972265875005251782037623241066309222400000000000000), (388507968779942656495361922435069267717860140827120511/2705965397226587500525178203762324106630922240000000000000)]
    reserve := (1148597/8000000000) }

theorem mixed_004_207_valid : mixed_004_207.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_207]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_207]
  · intro i; fin_cases i <;> norm_num [mixed_004_207]
  · norm_num [mixed_004_207]
  · norm_num [mixed_004_207, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_207, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_207, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_207, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_207]

def mixed_004_208 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(9/256), (91/2560)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(3022683/20000000), (7575619/50000000), (8626953/100000000), (7165261/50000000), (7165261/50000000), (3271053/20000000), (3218417/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1069903/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5578283/100000000), (747/50000000), (4405513/100000000), (2113273/50000000), (1/100000000), (1098921/20000000), (37343/12500000)]
    alternative := .zero
    polynomial := [(-20356428191891839339812512707279690851012404177/10613476310111628253332375109186980000000000000), (8129219069947/74700000000), (-8200801485874680840631364473295341438752861591677/5306738155055814126666187554593490000000000000), (8129219069947/74700000000), (-16381246543557469841922916433883403186654710779177/10613476310111628253332375109186980000000000000)]
    bernstein := [(12075190241943281464744829157766047165321092828117047/45584533648800197457372154111962508249006080000000000000), (14911971036334844178366498156664849364116609455850621/50649481832000219397080171235513898054451200000000000000), (3892470633759480569898824669188780198151848183441537357/13675360094640059237211646233588752474701824000000000000000), (10737501270878264322354723312683719299292895008925931277/45584533648800197457372154111962508249006080000000000000000), (67084962590609491130699798808950403912929989143470886503/455845336488001974573721541119625082490060800000000000000000)]
    reserve := (7358303/50000000000) }

theorem mixed_004_208_valid : mixed_004_208.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_208]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_208]
  · intro i; fin_cases i <;> norm_num [mixed_004_208]
  · norm_num [mixed_004_208]
  · norm_num [mixed_004_208, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_208, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_208, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_208, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_208]

def mixed_004_209 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(91/2560), (23/640)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(1890041/12500000), (1515901/10000000), (8628571/100000000), (14328677/100000000), (14328677/100000000), (16350159/100000000), (8042289/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(4329/400000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(348631/6250000), (299/20000000), (2203711/50000000), (4226357/100000000), (1/100000000), (343333/6250000), (75471/25000000)]
    alternative := .zero
    polynomial := [(-1644610852548787917082822274465756687679561727/838556648539792525334552780090300000000000000), (15821087943/143750000), (-648122899447852846765653857470987534137581311727/419278324269896262667276390045150000000000000), (15821087943/143750000), (-1294601188043156905614224892667509311587483061727/838556648539792525334552780090300000000000000)]
    bernstein := [(9670781385808401358762406299839888496822189133567495953/36015733813217750509371556492737184268288000000000000000000), (2683626150288278576888244418928054869399657604504675909/9003933453304437627342889123184296067072000000000000000000), (176972918864843674564758465000466770114038595085756721/613904553634393474591560622035292913664000000000000000000), (134600665004745580194352390029689222211877671080717981/562745840831527351708930570199018504192000000000000000000), (21213041113252980122077464672735291219383278427740993/140686460207881837927232642549754626048000000000000000000)]
    reserve := (18847799/125000000000) }

theorem mixed_004_209_valid : mixed_004_209.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_209]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_209]
  · intro i; fin_cases i <;> norm_num [mixed_004_209]
  · norm_num [mixed_004_209]
  · norm_num [mixed_004_209, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_209, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_209, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_209, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_209]

def mixed_004_210 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(23/640), (93/2560)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(15127239/100000000), (15166791/100000000), (8630189/100000000), (14326829/100000000), (14326829/100000000), (2043131/12500000), (643083/4000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1094609/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(697239/12500000), (187/12500000), (4409333/100000000), (528271/12500000), (1/100000000), (5492049/100000000), (15251/5000000)]
    alternative := .zero
    polynomial := [(-283352838576405660049655062691730101525964061/141323103520408848883599890079450000000000000), (16649808538119/149600000000), (-109261086134047710915822334568768679930390432811/70661551760204424441799945039725000000000000), (16649808538119/149600000000), (-218238819429519016171595014074845629759254901561/141323103520408848883599890079450000000000000)]
    bernstein := [(6452517433525565893744343723273575883300944400543399/23710082335522596660315142134391898112000000000000000000), (28613037030698871159755238398378847967096674699012109/94840329342090386641260568537567592448000000000000000000), (332239654127189761042261521636190204167848169082044557/1138083952105084639695126822450811109376000000000000000000), (368491451868340136365797285231970915467817321477638629/1517445269473446186260169096601081479168000000000000000000), (937287096460916547080160736585383692720012930169880439/6069781077893784745040676386404325916672000000000000000000)]
    reserve := (772093/5000000000) }

theorem mixed_004_210_valid : mixed_004_210.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_210]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_210]
  · intro i; fin_cases i <;> norm_num [mixed_004_210]
  · norm_num [mixed_004_210]
  · norm_num [mixed_004_210, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_210, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_210, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_210, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_210]

def mixed_004_211 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(93/2560), (47/1280)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(302683/2000000), (15174581/100000000), (8631807/100000000), (14324977/100000000), (14324977/100000000), (16339931/100000000), (16069577/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1106979/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5577729/100000000), (187/12500000), (2205623/50000000), (2112989/50000000), (1/100000000), (343173/6250000), (308153/100000000)]
    alternative := .zero
    polynomial := [(-11712537545574176639661389330251533230562489501/5711688791998508436251659194462100000000000000), (16846022675183/149600000000), (-260007010266538642299029338391965073676270300853/167990846823485542242695858660650000000000000), (16846022675183/149600000000), (-8828525811516739661527336115996560971762627739501/5711688791998508436251659194462100000000000000)]
    bernstein := [(67658283721506447179796204461794672340024328019069322499/245315165665633402144809770659524238114816000000000000000000), (37460462194642544145010294384396289021206273955214215921/122657582832816701072404885329762119057408000000000000000000), (54395904915949543901961734567817236427236918503493009377/183986374249225051608607327994643178586112000000000000000000), (7559840099707061978171690867555975326893177568062036361/30664395708204175268101221332440529764352000000000000000000), (2423315554383607909334170019080802679734451625628609619/15332197854102087634050610666220264882176000000000000000000)]
    reserve := (158054023/1000000000000) }

theorem mixed_004_211_valid : mixed_004_211.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_211]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_211]
  · intro i; fin_cases i <;> norm_num [mixed_004_211]
  · norm_num [mixed_004_211]
  · norm_num [mixed_004_211, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_211, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_211, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_211, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_211]

def mixed_004_212 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(47/1280), (19/512)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(757053/5000000), (759119/5000000), (345337/4000000), (7161561/50000000), (7161561/50000000), (2041851/12500000), (16062083/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1119361/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1394387/25000000), (1497/100000000), (4413161/100000000), (1056447/25000000), (1/100000000), (2744743/50000000), (77821/25000000)]
    alternative := .zero
    polynomial := [(-36298543327612467747186757887042272277773883601/17322870491898069368173298466095325000000000000), (8521326967841/74850000000), (-13409687555114154402999278248251964595519786133601/8661435245949034684086649233047662500000000000), (8521326967841/74850000000), (-26783076566900696338251369738616886918761798383601/17322870491898069368173298466095325000000000000)]
    bernstein := [(12995816223300426283704162243754417483331087026702157519/46500726397216025563652312607703991058432000000000000000000), (638806312672055040119005376720691005232774846746342747/2066698950987378913940102782564621824819200000000000000000), (6681426221235523476586541129042904215076169520763967637/22320348670663692270553110051697915708047360000000000000000), (33162076787138437463609674411726172186967266935117/132533800464120491475116811707550898585600000000000000), (7700300409597746448604916571717438888200162752061399/47616743830749210177179968110288886843834368000000000000)]
    reserve := (40428533/250000000000) }

theorem mixed_004_212_valid : mixed_004_212.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_212]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_212]
  · intro i; fin_cases i <;> norm_num [mixed_004_212]
  · norm_num [mixed_004_212]
  · norm_num [mixed_004_212, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_212, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_212, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_212, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_212]

def mixed_004_213 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(19/512), (3/80)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(236687/1562500), (3797547/25000000), (2158761/25000000), (14321263/100000000), (14321263/100000000), (16329679/100000000), (3210919/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(226351/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5577369/100000000), (749/50000000), (2207539/50000000), (4225597/100000000), (1/100000000), (2744101/50000000), (314411/100000000)]
    alternative := .zero
    polynomial := [(-1028165312495684459985420342403294531254535470541/480294308772286612962121596131457900000000000000), (6734246401/58515625), (-371908936289775887797419820848669970384792073970541/240147154386143306481060798065728950000000000000), (6734246401/58515625), (-12589656055373832053133122395846383834547959533399/8140581504615027338341044002228100000000000000)]
    bernstein := [(373832438691247708589305358283651827166917253495074459/1320222943124414024838990042982356350272536576000000000000), (322624257047736248293960632205719339263610925653077303/1031424174315948456905460971079965898650419200000000000000), (732586952067331647521493031785837277145579311546120457/2417400408553004195872174150968670074961920000000000000000), (4567057769992976536249794827607896362286508632731061/17986610182686043124048914813754985676800000000000000000), (3253769761685606495122030981573270909053887424202979/19672854887312859666928500577544515584000000000000000000)]
    reserve := (82696939/500000000000) }

theorem mixed_004_213_valid : mixed_004_213.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_213]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_213]
  · intro i; fin_cases i <;> norm_num [mixed_004_213]
  · norm_num [mixed_004_213]
  · norm_num [mixed_004_213, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_213, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_213, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_213, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_213]

def mixed_004_214 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/80), (97/2560)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(3788719/25000000), (3039601/20000000), (8636663/100000000), (14319401/100000000), (14319401/100000000), (255071/1562500), (16047111/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1144161/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(697149/12500000), (1499/100000000), (2208499/50000000), (845081/20000000), (1/100000000), (1371729/25000000), (158767/50000000)]
    alternative := .zero
    polynomial := [(-15479146618274182421666385518077691153676586483/7079459385100412934576526170564450000000000000), (17437073837583/149900000000), (-5483535939896823148476285920188043329607037586483/3539729692550206467288263085282225000000000000), (17437073837583/149900000000), (-10951592733175372114530905454858008968060398586483/7079459385100412934576526170564450000000000000)]
    bernstein := [(2868415946035838195850545137294810617448049930113/9999126083231479786215672825735168000000000000000000), (101277935492996373801470479049159535280966324925387/319972034663407353158901530423525376000000000000000000), (273280247783747464167570730106410711924698056035321631/890802144502926071194381860699094646784000000000000000000), (2448078185294044179358376796991806423034027410299996423/9501889541364544759406739847457009565696000000000000000000), (51417583120248938578085825175491092108587662073624772877/304060465323665432301015675118624306102272000000000000000000)]
    reserve := (10568947/62500000000) }

theorem mixed_004_214_valid : mixed_004_214.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_214]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_214]
  · intro i; fin_cases i <;> norm_num [mixed_004_214]
  · norm_num [mixed_004_214]
  · norm_num [mixed_004_214, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_214, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_214, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_214, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_214]

def mixed_004_215 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(97/2560), (49/1280)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(7580891/50000000), (15205831/100000000), (8638283/100000000), (2863507/20000000), (2863507/20000000), (16319403/100000000), (16039631/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1156579/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5577017/100000000), (1499/100000000), (4418919/100000000), (4225213/100000000), (1/100000000), (1371407/25000000), (64131/20000000)]
    alternative := .zero
    polynomial := [(-1022389958349842363961858783136365552120126477317/457595103387681338133455444619063900000000000000), (17634831625887/149900000000), (-354782721664297676878108518240757006832487309177317/228797551693840669066727722309531950000000000000), (17634831625887/149900000000), (-708543053370245511392255177698377648112854491877317/457595103387681338133455444619063900000000000000)]
    bernstein := [(5710987259369572133909132939338873993729975655516138459323/19653560038598301565527088181120186286342144000000000000000000), (12059371905494753651838670456896969308145385201913557231/37650498158234294186833502262682349207552000000000000000000), (4577984692582952380515996588595556522006325458565380037841/14740170028948726174145316135840139714756608000000000000000000), (2460687428322028614886686879191797120607676060089940559/9412624539558573546708375565670587301888000000000000000000), (212297776965149004268133480540766099910290457410813775483/1228347502412393847845443011320011642896384000000000000000000)]
    reserve := (172832017/1000000000000) }

theorem mixed_004_215_valid : mixed_004_215.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_215]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_215]
  · intro i; fin_cases i <;> norm_num [mixed_004_215]
  · norm_num [mixed_004_215]
  · norm_num [mixed_004_215, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_215, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_215, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_215, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_215]

def mixed_004_216 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(49/1280), (5/128)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(758607/5000000), (15217587/100000000), (1080089/12500000), (1431473/10000000), (1431473/10000000), (16311681/100000000), (16028421/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(293807/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2788379/50000000), (3/100000), (884361/20000000), (4224923/100000000), (1/100000000), (2741847/50000000), (81721/25000000)]
    alternative := .zero
    polynomial := [(-3093461315692452155798866835976905317718447/2683229500522393590689484053700000000000000), (1498358738403/25000000000), (-1046345791599554150800460580819692122985453447/1341614750261196795344742026850000000000000), (1498358738403/25000000000), (-2089598121883415849445122294803407340653188447/2683229500522393590689484053700000000000000)]
    bernstein := [(1687872459730586991425771593953918856376464468736353/7202739345253809617282090063596879872000000000000000000), (14167618728344226175088944444784114369513561044667/48018262301692064115213933757312532480000000000000000), (59729848772869625683356577318626880858212397975627/216082180357614288518462701907906396160000000000000000), (85691865372760124913136896974668563780746938403/480182623016920641152139337573125324800000000000000), (823885546950918832864398254899261712666821393/720273934525380961728209006359687987200000000000000)]
    reserve := (22877/20000000000) }

theorem mixed_004_216_valid : mixed_004_216.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_216]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_216]
  · intro i; fin_cases i <;> norm_num [mixed_004_216]
  · norm_num [mixed_004_216]
  · norm_num [mixed_004_216, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_216, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_216, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_216, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_216]

def mixed_004_217 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(5/128), (51/1280)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(7592973/50000000), (3046659/20000000), (540247/6250000), (14310977/100000000), (14310977/100000000), (16301363/100000000), (16013489/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(600067/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2788209/50000000), (3003/100000000), (4425661/100000000), (844907/20000000), (1/100000000), (5481109/100000000), (166553/50000000)]
    alternative := .zero
    polynomial := [(-163477832414134392618973400884764328500823401799/136103506207493959801413525015537300000000000000), (382496093/6250000), (-53119508580044618695047424397557486539107780151799/68051753103746979900706762507768650000000000000), (382496093/6250000), (-106075539327675102997475875394230208749714736901799/136103506207493959801413525015537300000000000000)]
    bernstein := [(8834438471638666165064789713847670017049073936849481/36535006752007471716538109032113162210508800000000000000), (597599443711127170592210792295979198473167090445383/1974865229838241714407465353087197957324800000000000000), (444678980170829273620629807250199138981413164379171037/1565786003657463073565918958519135523307520000000000000000), (36729373634143151187477562080925813942945879387871287/197486522983824171440746535308719795732480000000000000000), (3125890207806452630937320933244741073265235185759780201/365350067520074717165381090321131622105088000000000000000000)]
    reserve := (2138969/250000000000) }

theorem mixed_004_217_valid : mixed_004_217.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_217]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_217]
  · intro i; fin_cases i <;> norm_num [mixed_004_217]
  · norm_num [mixed_004_217]
  · norm_num [mixed_004_217, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_217, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_217, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_217, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_217]

def mixed_004_218 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(51/1280), (13/320)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(3799937/25000000), (7624519/50000000), (4323597/50000000), (1430721/10000000), (1430721/10000000), (16291023/100000000), (999911/6250000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(9571/781250), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2788043/50000000), (1503/50000000), (2214763/50000000), (264009/6250000), (1/100000000), (2739259/50000000), (67863/20000000)]
    alternative := .zero
    polynomial := [(-6328216763080006353895380902276808560178169357/5060903799731076592561673896725900000000000000), (293399951629/4696875000), (-219655869196972636672264830242144346846589174373/281161322207282032920092994262550000000000000), (293399951629/4696875000), (-3947477428782427453746871563456321434678426969357/5060903799731076592561673896725900000000000000)]
    bernstein := [(3387556922200601479918947755226267506580453902066356643/13585260192529442224952191405909138735104000000000000000000), (1053688377277035960120541522585561722294443874858558109/3396315048132360556238047851477284683776000000000000000000), (82548937097430378715057567195316659799750415252846689/283026254011030046353170654289773723648000000000000000000), (41097549691876900600214015568895442420607042551221021/212269690508272534764877990717330292736000000000000000000), (852859389902666341017466768192155590455065302876323/53067422627068133691219497679332573184000000000000000000)]
    reserve := (16071241/1000000000000) }

theorem mixed_004_218_valid : mixed_004_218.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_218]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_218]
  · intro i; fin_cases i <;> norm_num [mixed_004_218]
  · norm_num [mixed_004_218]
  · norm_num [mixed_004_218, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_218, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_218, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_218, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_218]

def mixed_004_219 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(13/320), (53/1280)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(7606773/50000000), (15264819/100000000), (2162609/25000000), (14303429/100000000), (14303429/100000000), (16280659/100000000), (7991841/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1250089/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5575761/100000000), (3009/100000000), (2216699/50000000), (3379/80000), (1/100000000), (68449/1250000), (345511/100000000)]
    alternative := .zero
    polynomial := [(-14317819263935128840496992717007571127556777/11007443800525361168180372725300000000000000), (6392857372389/100300000000), (-4303494737904637786288701037101132806443556777/5503721900262680584090186362650000000000000), (6392857372389/100300000000), (-8592671656545340443736905081485258041759556777/11007443800525361168180372725300000000000000)]
    bernstein := [(272109490815523291435075504216397318136344433667/1058912054181622120393202065211392000000000000000000), (1346729907070615094884914834700541804577279681627/4235648216726488481572808260845568000000000000000000), (1658712128318312715505831145411303323464924620939749/5540227867478246933897233205186002944000000000000000000), (1486937869511446857787641978151947285486058204509423/7386970489970995911862977606914670592000000000000000000), (698417308507567966539547938193936481289158801597863/29547881959883983647451910427658682368000000000000000000)]
    reserve := (23636797/1000000000000) }

theorem mixed_004_219_valid : mixed_004_219.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_219]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_219]
  · intro i; fin_cases i <;> norm_num [mixed_004_219]
  · norm_num [mixed_004_219]
  · norm_num [mixed_004_219, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_219, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_219, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_219, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_219]

def mixed_004_220 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(53/1280), (27/640)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(761367/5000000), (3820159/25000000), (108171/1250000), (7149817/50000000), (14299633/100000000), (254223/1562500), (3193761/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(637569/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1393861/25000000), (753/25000000), (27733/625000), (2111677/50000000), (1/100000000), (1094663/20000000), (70339/20000000)]
    alternative := .zero
    polynomial := [(-159981336811358237900815883541924071309218703/118319253715017122780171989463025000000000000), (203969955303/3137500000), (-46299103251907698936678855778407331781247718703/59159626857508561390085994731512500000000000), (203969955303/3137500000), (-92438225167004039635456895673272739491186218703/118319253715017122780171989463025000000000000)]
    bernstein := [(84056185283948370048320800160209646814664822499420257/317610828245703154013034557499343110144000000000000000000), (7389662033038550729682471719521289718921985524202009/22686487731835939572359611249953079296000000000000000000), (73177590662774244152929299859437162371411986426675651/238208121184277365509775918124507332608000000000000000000), (1185684013457641719935545271998567267190718850715129/5671621932958984893089902812488269824000000000000000000), (621080615018943490749107670516792065728250426028577/19850676765356447125814659843708944384000000000000000000)]
    reserve := (31287629/1000000000000) }

theorem mixed_004_220_valid : mixed_004_220.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_220]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_220]
  · intro i; fin_cases i <;> norm_num [mixed_004_220]
  · norm_num [mixed_004_220]
  · norm_num [mixed_004_220, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_220, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_220, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_220, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_220]

def mixed_004_221 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(27/640), (11/256)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(15241129/100000000), (1529649/10000000), (346277/4000000), (893489/6250000), (893489/6250000), (812993/5000000), (15953947/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(260047/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2787567/50000000), (603/20000000), (444117/10000000), (844591/20000000), (1/100000000), (341919/6250000), (178933/50000000)]
    alternative := .zero
    polynomial := [(-3344417837611177677268270666668355015657057/2381141131226570164705143239745000000000000), (55514538821/837500000), (-932586846800456714987421283405042171763557057/1190570565613285082352571619872500000000000), (55514538821/837500000), (-1861829275763302252297574296143415988511457057/2381141131226570164705143239745000000000000)]
    bernstein := [(108826639843117342494325618993009133361032935233263/399489190850725125924137644441416499200000000000000000), (53307249406274951094117213560922410067374774487839/159795676340290050369655057776566599680000000000000000), (60421880465720577254992287110314387995501797413613/191754811608348060443586069331879919616000000000000000), (5545977296653408652215158851903023114249153935487/25567308214446408059144809244250655948800000000000000), (399252814710611412902389437000462157977988633007/10226923285778563223657923697700262379520000000000000)]
    reserve := (19519693/500000000000) }

theorem mixed_004_221_valid : mixed_004_221.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_221]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_221]
  · intro i; fin_cases i <;> norm_num [mixed_004_221]
  · norm_num [mixed_004_221]
  · norm_num [mixed_004_221, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_221, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_221, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_221, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_221]

def mixed_004_222 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(11/256), (7/160)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(7627457/50000000), (7656191/50000000), (866017/10000000), (14292001/100000000), (14292001/100000000), (8124713/50000000), (7969553/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1325379/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5574831/100000000), (1509/50000000), (4445069/100000000), (4222553/100000000), (1/100000000), (2734043/50000000), (14561/4000000)]
    alternative := .zero
    polynomial := [(-8039544836609772464793484878208102190252443421/5513993548022047770974365471325850000000000000), (3398486331099/50300000000), (-720511056681392124431143325726556498158955087807/918998924670341295162394245220975000000000000), (3398486331099/50300000000), (-4315026795251742974122066469481130886763478083421/5513993548022047770974365471325850000000000000)]
    bernstein := [(2212274193320730525010785164118607988052671950026257/7894140653036566887761532584565383836467200000000000000), (5055055123136951487981113007164346519743320978776911/14801513724443562914552873596060094693376000000000000000), (996181583161172563444785664712472040104988414122761/3083648692592408940531848665845853061120000000000000000), (99992350658077816773215382968913360473977422830579/444757022970058981807478172958536499200000000000000000), (4339156335174968120410534110646274110550915501061/92657713118762287876557952699695104000000000000000000)]
    reserve := (365859/7812500000) }

theorem mixed_004_222_valid : mixed_004_222.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_222]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_222]
  · intro i; fin_cases i <;> norm_num [mixed_004_222]
  · norm_num [mixed_004_222]
  · norm_num [mixed_004_222, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_222, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_222, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_222, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_222]

def mixed_004_223 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(7/160), (57/1280)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(3053739/20000000), (1532831/10000000), (8663417/100000000), (14288163/100000000), (14288163/100000000), (2029871/12500000), (15924283/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1350571/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1114907/20000000), (3021/100000000), (278061/6250000), (4222149/100000000), (1/100000000), (5465461/100000000), (92543/25000000)]
    alternative := .zero
    polynomial := [(-11204279549673414889442805117403344363982597931/7407465080829818987120091912196700000000000000), (1299886592681/18881250000), (-2906438042020375039091341754899864577331074597931/3703732540414909493560045956098350000000000000), (1299886592681/18881250000), (-5801671804491076663293240704682325810298166597931/7407465080829818987120091912196700000000000000)]
    bernstein := [(4196571066387802305549087434267992388193170826744607/14563668946117890514197070306731687936000000000000000000), (40724201049995396356118024142760516631101836216980257/116509351568943124113576562453853503488000000000000000000), (28055068903650578180998180721799102962720467356645437/84734073868322272082601136330075275264000000000000000000), (1736075336205870661177096658632343349643141461328868257/7456598500412359943268899997046624223232000000000000000000), (1087930322339512980567146380415101155176391539861106869/19884262667766293182050399992124331261952000000000000000000)]
    reserve := (54713133/1000000000000) }

theorem mixed_004_223_valid : mixed_004_223.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_223]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_223]
  · intro i; fin_cases i <;> norm_num [mixed_004_223]
  · norm_num [mixed_004_223]
  · norm_num [mixed_004_223, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_223, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_223, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_223, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_223]

def mixed_004_224 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(57/1280), (29/640)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(1910309/12500000), (3836069/25000000), (1733333/20000000), (14284311/100000000), (14284311/100000000), (16228487/100000000), (7954739/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1375811/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2787123/50000000), (189/6250000), (1113223/25000000), (4221743/100000000), (1/100000000), (546283/10000000), (188153/50000000)]
    alternative := .zero
    polynomial := [(-33931731954655240512015905441605632982243129/21637815494550168625748174416387500000000000), (1060352211539/15120000000), (-2832589546815103705896830300221637302599268543/3606302582425028104291362402731250000000000), (1060352211539/15120000000), (-16961605548935966994868965895888218182613368129/21637815494550168625748174416387500000000000)]
    bernstein := [(120404709677210686932572226503973395360579747597625497/406584980838640802095072317844135870464000000000000000000), (24234079793093080681051013670767689904014449396890303/67764163473106800349178719640689311744000000000000000000), (11493298395291174328839146296598510456680643513978491/33882081736553400174589359820344655872000000000000000000), (4081110292453617551075754843109542862729641607205927/16941040868276700087294679910172327936000000000000000000), (1592636890022946255483566818444578316204938807467657/25411561302415050130942019865258491904000000000000000000)]
    reserve := (3917107/62500000000) }

theorem mixed_004_224_valid : mixed_004_224.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_224]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_224]
  · intro i; fin_cases i <;> norm_num [mixed_004_224]
  · norm_num [mixed_004_224]
  · norm_num [mixed_004_224, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_224, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_224, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_224, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_224]

def mixed_004_225 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(29/640), (59/1280)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(3824061/25000000), (15360279/100000000), (4334957/50000000), (2856089/20000000), (2856089/20000000), (8108991/50000000), (15894691/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1401099/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1114793/20000000), (1513/50000000), (4456817/100000000), (4221333/100000000), (1/100000000), (5460193/100000000), (382427/100000000)]
    alternative := .zero
    polynomial := [(-5385015960093692215152639671686524786606669558449/3313096767389795929355259581451421950000000000000), (21617466216553/302600000000), (-1302782594389323530614779509123544861620697456558449/1656548383694897964677629790725710975000000000000), (21617466216553/302600000000), (-2600180172818553369014406378575403198454788243558449/3313096767389795929355259581451421950000000000000)]
    bernstein := [(169084829277536701843747886419602470814979709855841900031/555845400954003625027139307340800995622912000000000000000000), (135562443728577759995019670005310613946380279508645395267/370563600636002416684759538227200663748608000000000000000000), (2317639316692736378090200928747846017115105422586932752013/6670144811448043500325671688089611947474944000000000000000000), (369223919228874488661816141709400611816585594757554426547/1482254402544009666739038152908802654994432000000000000000000), (628894257273801614630533094432647377086843913834088207711/8893526415264058000434228917452815929966592000000000000000000)]
    reserve := (70713711/1000000000000) }

theorem mixed_004_225_valid : mixed_004_225.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_225]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_225]
  · intro i; fin_cases i <;> norm_num [mixed_004_225]
  · norm_num [mixed_004_225]
  · norm_num [mixed_004_225, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_225, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_225, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_225, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_225]

def mixed_004_226 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(59/1280), (3/64)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(15310013/100000000), (48051/312500), (2168291/25000000), (3569141/25000000), (3569141/25000000), (8103727/50000000), (15879921/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(285287/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(557369/10000000), (3029/100000000), (4460751/100000000), (2110461/50000000), (1/100000000), (1364387/25000000), (77707/20000000)]
    alternative := .zero
    polynomial := [(-47270553744111337321150018871306335063337224691/28084963334186812812934736016196650000000000000), (11014760790309/151450000000), (-11054004454922384573349321620614508528183744524691/14042481667093406406467368008098325000000000000), (11014760790309/151450000000), (-1696979873546204446875191786335208517023396294207/2160381794937447139456518155092050000000000000)]
    bernstein := [(23547095162275594296642747916623159824064157594630586749/75389999393557174866267785607473711284224000000000000000000), (201441000207065007991078093040209463474029790162407459/538499995668265534759055611481955080601600000000000000000), (28735456167150663199606706242959201176555638411718401/80774999350239830213858341722293262090240000000000000000), (69287515665133963531073473968374584112689550900119/269249997834132767379527805740977540300800000000000000), (114294344266322679128998282546325480407356259513/1449807680645330285889765107836032909312000000000000)]
    reserve := (78834141/1000000000000) }

theorem mixed_004_226_valid : mixed_004_226.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_226]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_226]
  · intro i; fin_cases i <;> norm_num [mixed_004_226]
  · norm_num [mixed_004_226]
  · norm_num [mixed_004_226, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_226, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_226, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_226, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_226]

def mixed_004_227 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/64), (61/1280)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(15323777/100000000), (7696199/50000000), (4338207/50000000), (1427267/10000000), (1427267/10000000), (16196903/100000000), (15865169/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1451819/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5573423/100000000), (379/12500000), (4464693/100000000), (4220507/100000000), (1/100000000), (5454897/100000000), (49329/12500000)]
    alternative := .zero
    polynomial := [(-247200366959325586166489629713021340943249/141909858026129716969816068300000000000000), (11221591128389/151600000000), (-215643209391558888363514646377680379848432889/273683297621821597013216703150000000000000), (11221591128389/151600000000), (-3012330521573922646262709829285273741672592723/3831566166705502358185033844100000000000000)]
    bernstein := [(91583954645779599015217767596970218806977373/285702280876045428674576358976782336000000000000), (32776340679211086732156582941595381123005786317/85710684262813628602372907693034700800000000000000), (138360453254768837818612754191295568720471570757/379998107569124461783919295190794240000000000000000), (136615927224192470271536544955416955030609601189251/514264105576881771614237446158208204800000000000000000), (895154715803672852944886231531981818962035335770557/10285282111537635432284748923164164096000000000000000000)]
    reserve := (87032587/1000000000000) }

theorem mixed_004_227_valid : mixed_004_227.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_227]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_227]
  · intro i; fin_cases i <;> norm_num [mixed_004_227]
  · norm_num [mixed_004_227]
  · norm_num [mixed_004_227, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_227, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_227, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_227, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_227]

def mixed_004_228 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(61/1280), (31/640)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(15337537/100000000), (7704257/50000000), (4339833/50000000), (14268761/100000000), (14268761/100000000), (2023291/12500000), (15850433/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(369313/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5573163/100000000), (607/20000000), (1117161/25000000), (422009/10000000), (1/100000000), (5452239/100000000), (80143/20000000)]
    alternative := .zero
    polynomial := [(-124574294317566270087253934041516406880029513/69136575433724246332016047780068750000000000), (11429235125919/151750000000), (-27263451480008466938315332949473410896371042013/34568287716862123166008023890034375000000000), (11429235125919/151750000000), (-54402328665699367606543411964905305385862054513/69136575433724246332016047780068750000000000)]
    bernstein := [(4694679956007657752888333186706857202339343822164859/14275929348330896801839273219354263552000000000000000000), (929884926332071343777390550834777261857069657188163/2379321558055149466973212203225710592000000000000000000), (51856937817830583122462934265403751117511403971750741/139190311146226243817932913888704069632000000000000000000), (2119327736218881304555260778934177375407693870991279/7732795063679235767662939660483559424000000000000000000), (1105822707471623939326967159018776016421016083354127/11599192595518853651494409490725339136000000000000000000)]
    reserve := (95336179/1000000000000) }

theorem mixed_004_228_valid : mixed_004_228.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_228]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_228]
  · intro i; fin_cases i <;> norm_num [mixed_004_228]
  · norm_num [mixed_004_228]
  · norm_num [mixed_004_228, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_228, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_228, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_228, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_228]

def mixed_004_229 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(31/640), (63/1280)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(3837823/25000000), (3856167/25000000), (8682919/100000000), (14264837/100000000), (14264837/100000000), (1617573/10000000), (3958929/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(375683/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5572909/100000000), (1519/50000000), (1118151/25000000), (421967/10000000), (1/100000000), (217983/4000000), (203393/50000000)]
    alternative := .zero
    polynomial := [(-157084518899335951783191943295631905884977019/84325320943469264080200610106730000000000000), (7421989797/96875000), (-33285113929691126191821110246427102325380777019/42162660471734632040100305053365000000000000), (7421989797/96875000), (-66413143340482916431859028549558572744876577019/84325320943469264080200610106730000000000000)]
    bernstein := [(4770992617149197200748723218359922612693051151623301/14147441237379076328345669590923922636800000000000000000), (11298336250501960939391712449046680189321154816819173/28294882474758152656691339181847845273600000000000000000), (3405017713048339663468929494184359596061230788201173/8935226044660469260007791320583530086400000000000000000), (31977553900775965167593990829792033307720969900913317/113179529899032610626765356727391381094400000000000000000), (23468550551392346859113438539020062557076070236391941/226359059798065221253530713454782762188800000000000000000)]
    reserve := (103678423/1000000000000) }

theorem mixed_004_229_valid : mixed_004_229.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_229]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_229]
  · intro i; fin_cases i <;> norm_num [mixed_004_229]
  · norm_num [mixed_004_229]
  · norm_num [mixed_004_229, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_229, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_229, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_229, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_229]

def mixed_004_230 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(63/1280), (1/20)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(3841261/25000000), (772043/5000000), (8686173/100000000), (142609/1000000), (142609/1000000), (16165109/100000000), (3164203/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(764131/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5572663/100000000), (3041/100000000), (4476573/100000000), (263703/6250000), (1/100000000), (680863/12500000), (82569/20000000)]
    alternative := .zero
    polynomial := [(-12026910604826392697763103836490243219431029347/6248045677591943084879431534034550000000000000), (473878059971/6082000000), (-145214491359938703516818578163526336972279663491/183766049340939502496453868648075000000000000), (473878059971/6082000000), (-4925265795633089526874068553723405213838077529347/6248045677591943084879431534034550000000000000)]
    bernstein := [(341055077883414152271434060591746154226416239908315949/986586465043071896420974652270202322944000000000000000000), (9717452026136210721783313883035509513025627516600681/23823820888824179316983762909933862912000000000000000000), (4787187075762843369503381305526761384837410961516871/12284157645799967460319752750434648064000000000000000000), (1693323793013219504230343175122205683392712413049/5816362521685590653560488991683072000000000000000000), (112124247376647382462764138745718514454303473053/999687308414710893580709045445528000000000000000000)]
    reserve := (56079659/500000000000) }

theorem mixed_004_230_valid : mixed_004_230.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_230]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_230]
  · intro i; fin_cases i <;> norm_num [mixed_004_230]
  · norm_num [mixed_004_230]
  · norm_num [mixed_004_230, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_230, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_230, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_230, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_230]

def mixed_004_231 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/20), (13/256)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(15378791/100000000), (1545709/10000000), (2172357/25000000), (3564237/25000000), (3564237/25000000), (3230893/20000000), (15806331/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1553839/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(696553/12500000), (761/25000000), (89611/2000000), (527353/12500000), (1/100000000), (5444227/100000000), (418891/100000000)]
    alternative := .zero
    polynomial := [(-421701270307393509159638716495314815579783/212117056832795533524081191820000000000000), (12057029105819/152200000000), (-83891185915974181919181658552884730254329783/106058528416397766762040595910000000000000), (12057029105819/152200000000), (-167360670561640970329203678389274145693079783/212117056832795533524081191820000000000000)]
    bernstein := [(12022532435995923622142873604899318055813817/33938729093247285363852990691200000000000000000), (60318427681568898138809967690727098168706087/144805244131188417552439426949120000000000000000), (6645872609373508580226599026906834144650509011/16681564123912905702041021984538624000000000000000), (1422429325201068664273107216399122491959822467/4744978239690782066358335142268764160000000000000), (4397658186231672849506066614167303814866796177/36441432880825206269632013892624108748800000000000)]
    reserve := (60338711/500000000000) }

theorem mixed_004_231_valid : mixed_004_231.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_231]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_231]
  · intro i; fin_cases i <;> norm_num [mixed_004_231]
  · norm_num [mixed_004_231]
  · norm_num [mixed_004_231, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_231, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_231, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_231, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_231]

def mixed_004_232 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(13/256), (33/640)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(7696267/50000000), (7736679/50000000), (2173171/25000000), (7126491/50000000), (7126491/50000000), (16143797/100000000), (986979/6250000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(789733/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(174131/3125000), (3047/100000000), (4484537/100000000), (1054599/25000000), (1/100000000), (5441543/100000000), (106231/25000000)]
    alternative := .zero
    polynomial := [(-99231028528017994560515097049660810814541670647/48351015006751934423940600286780100000000000000), (6133969316811/76175000000), (-19141491004909942457632405296357104829535125670647/24175507503375967211970300143390050000000000000), (6133969316811/76175000000), (-38183750981291866920704295495664548848255709670647/48351015006751934423940600286780100000000000000)]
    bernstein := [(4324559497376380786422540226368418274663751557769/11917706064987361695010701731898350108672000000000000), (371094315190495237841236693319435408226906416855823/872546336900860409813283519656843490099200000000000000), (528502379261410826608839759385829486410650371293581617/1297912676140029859597259235489554691522560000000000000000), (143020697719065667150155623081767160708141081037510339/463540241478582092713306869817698104115200000000000000000), (1049104841686630591525398555503534069042396153158725513/8111954225875186622482870221809716822016000000000000000000)]
    reserve := (129328249/1000000000000) }

theorem mixed_004_232_valid : mixed_004_232.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_232]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_232]
  · intro i; fin_cases i <;> norm_num [mixed_004_232]
  · norm_num [mixed_004_232]
  · norm_num [mixed_004_232, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_232, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_232, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_232, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_232]

def mixed_004_233 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(33/640), (67/1280)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(15406273/100000000), (3097933/20000000), (434797/5000000), (14249001/100000000), (14249001/100000000), (8066553/50000000), (3155403/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(80257/5000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2785983/50000000), (61/2000000), (1122133/25000000), (2108983/50000000), (1/100000000), (1359713/25000000), (86189/20000000)]
    alternative := .zero
    polynomial := [(-4990534897484226221960443498692135462686956397/2356648474103418693858221516367450000000000000), (31199150837/381250000), (-933894251953920182706706053020355557822410981397/1178324237051709346929110758183725000000000000), (31199150837/381250000), (-1862797969010356139191451662542018980182135006397/2356648474103418693858221516367450000000000000)]
    bernstein := [(146919870353869474675679604074971916909718107191149763/395380004861034617652972557559442440192000000000000000000), (343295852566461685204081089176745790957305833390440937/790760009722069235305945115118884880384000000000000000000), (1974012541719371033965759005184836471514668168865383889/4744560058332415411835670690713309282304000000000000000000), (1003803199713591144811996265326777387038701194359463537/3163040038888276941223780460475539521536000000000000000000), (873072757620654208133480078140179422251580975253344563/6326080077776553882447560920951079043072000000000000000000)]
    reserve := (138011651/1000000000000) }

theorem mixed_004_233_valid : mixed_004_233.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_233]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_233]
  · intro i; fin_cases i <;> norm_num [mixed_004_233]
  · norm_num [mixed_004_233]
  · norm_num [mixed_004_233, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_233, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_233, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_233, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_233]

def mixed_004_234 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(67/1280), (17/320)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(15420007/100000000), (1550601/10000000), (4349599/50000000), (7122503/50000000), (7122503/50000000), (2015299/12500000), (15762381/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(101929/6250000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1392937/25000000), (3053/100000000), (4492537/100000000), (4217533/100000000), (1/100000000), (1087231/20000000), (218477/50000000)]
    alternative := .zero
    polynomial := [(-1390949776581618618960921232677424765131260717/636859062271037170480162334147287500000000000), (12692219295513/152650000000), (-252628378180117706593754054214408553097754635717/318429531135518585240081167073643750000000000), (12692219295513/152650000000), (-503865806583653794568547187196139681430378010717/636859062271037170480162334147287500000000000)]
    bernstein := [(650292192766174891589043632709690213051101142259837843/1709555527884582584507921151208514912256000000000000000000), (2744298166787805999660323676958319944438014911113997/6194041767697762987347540402929401856000000000000000000), (136237566411725341548076678725670374946155487567262929/320541661478359234595235215851596546048000000000000000000), (2905195619540012381089586622374073761983867651286131/8903935041065534294312089329211015168000000000000000000), (980471055208105185626984159636501798419611887763043/6677951280799150720734066996908261376000000000000000000)]
    reserve := (146822133/1000000000000) }

theorem mixed_004_234_valid : mixed_004_234.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_234]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_234]
  · intro i; fin_cases i <;> norm_num [mixed_004_234]
  · norm_num [mixed_004_234]
  · norm_num [mixed_004_234, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_234, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_234, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_234, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_234]

def mixed_004_235 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(17/320), (69/1280)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(15433737/100000000), (15522393/100000000), (8702457/100000000), (3560249/25000000), (3560249/25000000), (8055827/50000000), (3149553/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1656637/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(348221/6250000), (191/6250000), (89931/2000000), (2108549/50000000), (1/100000000), (5433451/100000000), (8859/2000000)]
    alternative := .zero
    polynomial := [(-45563298753733512909295288195146678104197433/20235812560522722010995641252700000000000000), (25811220912021/305600000000), (-8035233327639920269845886227973704865814028683/10117906280261361005497820626350000000000000), (25811220912021/305600000000), (-16024903356526107026782477167752263053523859933/20235812560522722010995641252700000000000000)]
    bernstein := [(82599382838483931986557367020997301401907793998307/212187873914626737554017655221911552000000000000000000), (383695560155651736358285298535414035432511715775999/848751495658506950216070620887646208000000000000000000), (4421168108368306268549676569815548851542764213004129/10185017947902083402592847450651754496000000000000000000), (4553510354943541935279365609141575942531083590041351/13580023930536111203457129934202339328000000000000000000), (8459391579602471763935523197381167990700433075758707/54320095722144444813828519736809357312000000000000000000)]
    reserve := (31146453/200000000000) }

theorem mixed_004_235_valid : mixed_004_235.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_235]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_235]
  · intro i; fin_cases i <;> norm_num [mixed_004_235]
  · norm_num [mixed_004_235]
  · norm_num [mixed_004_235, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_235, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_235, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_235, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_235]

def mixed_004_236 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(69/1280), (7/128)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(1930933/12500000), (121397/781250), (8705717/100000000), (14236973/100000000), (3559243/25000000), (8050447/50000000), (3146633/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(841229/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5571331/100000000), (3059/100000000), (4500573/100000000), (210833/5000000), (1/100000000), (271537/5000000), (448933/100000000)]
    alternative := .zero
    polynomial := [(-222252409883181479167397078309054351149655983/95787758975596179883491465199450000000000000), (13119830396599/152950000000), (-38074135469176115524562850149095757083383155983/47893879487798089941745732599725000000000000), (13119830396599/152950000000), (-10846574075495578509994043317126065687945236569/13683965567942311411927352171350000000000000)]
    bernstein := [(102401783509802772915931621590811568193215568991046657/257128307598322534188830583329224916992000000000000000000), (1693984479259488559210738875761815521548241036785293/3673261537118893345554722618988927385600000000000000000), (3418915425480774354758182293139639347552301389367307/7713849227949676025664917499876747509760000000000000000), (88553975809567699323667486090218941557412877933603/257128307598322534188830583329224916992000000000000000), (4234661289895142153705917939714145467702333955313/25712830759832253418883058332922491699200000000000000)]
    reserve := (16469059/100000000000) }

theorem mixed_004_236_valid : mixed_004_236.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_236]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_236]
  · intro i; fin_cases i <;> norm_num [mixed_004_236]
  · norm_num [mixed_004_236]
  · norm_num [mixed_004_236, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_236, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_236, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_236, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_236]

def mixed_004_237 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(7/128), (71/1280)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(3092237/20000000), (15555277/100000000), (8708977/100000000), (7116467/50000000), (7116467/50000000), (1609011/10000000), (7859291/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1708329/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5571133/100000000), (1531/50000000), (900921/20000000), (4216219/100000000), (1/100000000), (5428023/100000000), (56863/12500000)]
    alternative := .zero
    polynomial := [(-3793671910482469531987005042138513367627765901/1587301720037098162562778300585710000000000000), (26669791398301/306200000000), (-631574613858948918216038749066197110662693515901/793650860018549081281389150292855000000000000), (26669791398301/306200000000), (-1259355555807415366900090493090255707957759265901/1587301720037098162562778300585710000000000000)]
    bernstein := [(173553857342936543448487622215528808363031557631411/426088061027742782184301521744630130933760000000000000), (2004172716196803726525490795584125033721014790056179/4260880610277427821843015217446301309337600000000000000), (57837173784933731970203695175174827125075434812538009/127826418308322834655290456523389039280128000000000000000), (150669388933774835679313949569825337913737463850676083/426088061027742782184301521744630130933760000000000000000), (740491832366540697333539007848767052532447217670781619/4260880610277427821843015217446301309337600000000000000000)]
    reserve := (5430889/31250000000) }

theorem mixed_004_237_valid : mixed_004_237.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_237]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_237]
  · intro i; fin_cases i <;> norm_num [mixed_004_237]
  · norm_num [mixed_004_237]
  · norm_num [mixed_004_237, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_237, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_237, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_237, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_237]

def mixed_004_238 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(71/1280), (9/160)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(15474903/100000000), (15571777/100000000), (4356119/50000000), (14228881/100000000), (14228881/100000000), (2009913/12500000), (3140803/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(216781/12500000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2785471/50000000), (613/20000000), (901729/20000000), (131743/3125000), (1/100000000), (54253/1000000), (230431/50000000)]
    alternative := .zero
    polynomial := [(-3744281680175803513962967368516967646271395567/1521523325699600271736571620549800000000000000), (13550794365323/153250000000), (-606026940092323780884041548925659850785503995567/760761662849800135868285810274900000000000000), (13550794365323/153250000000), (-1208309598504471758254120130482802733924736595567/1521523325699600271736571620549800000000000000)]
    bernstein := [(1701066721332878276751115548834254715506278373486092273/4084308077488087179613305148389445337088000000000000000000), (18837142717043636831065714173912447934295001394779259/39272193052770069034743318734513897472000000000000000000), (88411394047086509513244113789317045258978221428691379/191451941132254086544373678830755250176000000000000000000), (222680990775393765583797752732472430575298920925019/613628016449532328667864355226779648000000000000000000), (182417895757980111745177758083485678917298439902513/997145526730490034085279577243516928000000000000000000)]
    reserve := (182940093/1000000000000) }

theorem mixed_004_238_valid : mixed_004_238.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_238]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_238]
  · intro i; fin_cases i <;> norm_num [mixed_004_238]
  · norm_num [mixed_004_238]
  · norm_num [mixed_004_238, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_238, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_238, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_238, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_238]

def mixed_004_239 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(9/160), (73/1280)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(1936077/12500000), (3897079/25000000), (8715501/100000000), (7112407/50000000), (7112407/50000000), (8034237/50000000), (1961183/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1760217/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2785379/50000000), (767/25000000), (902539/20000000), (421533/10000000), (1/100000000), (5422569/100000000), (58351/12500000)]
    alternative := .zero
    polynomial := [(-184008775177991471772282442584860219800085399/72648616122171438185024492153850000000000000), (6883772343919/76700000000), (-28966210534310009094652830784218778606154585399/36324308061085719092512246076925000000000000), (6883772343919/76700000000), (-57748412293442026717533379125852696992509085399/72648616122171438185024492153850000000000000)]
    bernstein := [(20269697421356967365704736616708868165802715324361/47610997061826273728937651177947136000000000000000000), (26609630363089139310436313941311489938650951915631/54412568070658598547357315631939584000000000000000000), (4307569596223808370684001289374659403002777527408347/9141311435870644555956029026165850112000000000000000000), (99725711124831644360030658420115481350464069109483/267877258194011562079297553880317952000000000000000000), (37483284977817746311318790226642748008870977923364041/195014643965240417193728619224871469056000000000000000000)]
    reserve := (192207539/1000000000000) }

theorem mixed_004_239_valid : mixed_004_239.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_239]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_239]
  · intro i; fin_cases i <;> norm_num [mixed_004_239]
  · norm_num [mixed_004_239]
  · norm_num [mixed_004_239, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_239, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_239, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_239, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_239]

def mixed_004_240 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(73/1280), (37/640)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(7751163/50000000), (7802447/50000000), (2179691/25000000), (14220733/100000000), (14220733/100000000), (16057621/100000000), (1567493/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(357247/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(278529/5000000), (3071/100000000), (2258377/50000000), (2107441/50000000), (1/100000000), (5419833/100000000), (472741/100000000)]
    alternative := .zero
    polynomial := [(-302020876377237092860435750236159917239894830191/115896085768631036340015663801397100000000000000), (559405665083/6142000000), (-46258017324165276879706997093220333386764131830191/57948042884315518170007831900698550000000000000), (559405665083/6142000000), (-92214013771953316666553558436204506856288368830191/115896085768631036340015663801397100000000000000)]
    bernstein := [(135359333324528991316600747186442614995078762676596110769/311106186319175827356846757596707239755776000000000000000000), (77546001809185684878868618534821357824584909261340743661/155553093159587913678423378798353619877888000000000000000000), (112172535865707656172553621582995483380625208656806848427/233329639739381870517635068197530429816832000000000000000000), (14846264015466741296055393786909728871310845651606804821/38888273289896978419605844699588404969472000000000000000000), (3919296906513574240898447690982329264627440420170248449/19444136644948489209802922349794202484736000000000000000000)]
    reserve := (201567031/1000000000000) }

theorem mixed_004_240_valid : mixed_004_240.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_240]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_240]
  · intro i; fin_cases i <;> norm_num [mixed_004_240]
  · norm_num [mixed_004_240]
  · norm_num [mixed_004_240, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_240, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_240, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_240, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_240]

def mixed_004_241 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(37/640), (15/256)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(1551603/10000000), (1952689/12500000), (2180507/25000000), (3554159/25000000), (3554159/25000000), (3209349/20000000), (3915103/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(906151/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5570409/100000000), (1537/50000000), (2260411/50000000), (4214431/100000000), (1/100000000), (5417089/100000000), (478661/100000000)]
    alternative := .zero
    polynomial := [(-872034017928197233850720646987120435787423902161/325362854250679212865666401459754980000000000000), (35508972067/384250000), (-129999865987039703933355645794655290864785105902161/162681427125339606432833200729877490000000000000), (35508972067/384250000), (-259127697956151210632860570942323461293782787902161/325362854250679212865666401459754980000000000000)]
    bernstein := [(143580490949165511671602281346432391460147050540897191/322998987227228597689778946818522166067200000000000000000), (170673184805202431607327058598544170345760619339029853/335918946716317741597370104691263052709888000000000000000), (12847999501016102993570134400532922735692502659689504101/26201677843872783844594868165918518111371264000000000000000), (5158961542405387397873988130673697060934804476546397/13183234135281903821179807882223153766727680000000000000), (294854598166513361164093091720768666837494683243889519/1397422818339881805045059635515654299273134080000000000000)]
    reserve := (210998843/1000000000000) }

theorem mixed_004_241_valid : mixed_004_241.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_241]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_241]
  · intro i; fin_cases i <;> norm_num [mixed_004_241]
  · norm_num [mixed_004_241]
  · norm_num [mixed_004_241, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_241, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_241, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_241, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_241]

def mixed_004_242 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(15/256), (19/320)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(15529731/100000000), (15638169/100000000), (8725293/100000000), (7106263/50000000), (7106263/50000000), (8017923/50000000), (1564591/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1838419/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1114049/20000000), (3077/100000000), (4524899/100000000), (4213977/100000000), (1/100000000), (5414339/100000000), (484569/100000000)]
    alternative := .zero
    polynomial := [(-463277624004729531658738612030911087612708388397/168125558249243891620300286608051950000000000000), (28845791944951/307700000000), (-67246261831011667727699092375589127188566691638397/84062779124621945810150143304025975000000000000), (28845791944951/307700000000), (-134029246038018605923739446139147343289520674888397/168125558249243891620300286608051950000000000000)]
    bernstein := [(327873006217762661502717446085981844375203593340430963/722093774302245531236958180681009895519027200000000000000), (93465573447074205395286467024924392232671902040401403/180523443575561382809239545170252473879756800000000000000), (241804752127757264625245601596810404709559889795579159/483544938148825132524748781706033412177920000000000000000), (113110703359182512457119442353953703058016299010552403/282067880586814660639436789328519490437120000000000000000), (388815863823131837184567987614158451729071936944772963/1762924253667591628996479933303246815232000000000000000000)]
    reserve := (27568957/125000000000) }

theorem mixed_004_242_valid : mixed_004_242.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_242]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_242]
  · intro i; fin_cases i <;> norm_num [mixed_004_242]
  · norm_num [mixed_004_242]
  · norm_num [mixed_004_242, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_242, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_242, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_242, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_242]

def mixed_004_243 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(19/320), (77/1280)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(15543427/100000000), (3130973/20000000), (8728559/100000000), (35521/250000), (35521/250000), (4006231/25000000), (15631423/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(372917/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5570087/100000000), (77/2500000), (2264493/50000000), (4213521/100000000), (1/100000000), (2705791/50000000), (98093/20000000)]
    alternative := .zero
    polynomial := [(-60529165470193657967705868851747217937029827/21373047603476808927942440236050000000000000), (5857223204341/61600000000), (-8557817321643225055364121810768487259699323577/10686523801738404463971220118025000000000000), (5857223204341/61600000000), (-17055105477816256452760537752685227301461617327/21373047603476808927942440236050000000000000)]
    bernstein := [(14845618587393081815791835797663630056934770168919/32016092519804711997751674589937664000000000000000000), (157629314691136588000141514924514918386836825024213/298816863518177311979015629506084864000000000000000000), (421917367366891951312318692985284445953921151472047/827492852819567940864966358632235008000000000000000000), (1963919149282024447445349994290939614067860767668757/4781069816290836991664250072097357824000000000000000000), (13206442459989140885405484396163251532262389850004193/57372837795490043899971000865168293888000000000000000000)]
    reserve := (230186321/1000000000000) }

theorem mixed_004_243_valid : mixed_004_243.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_243]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_243]
  · intro i; fin_cases i <;> norm_num [mixed_004_243]
  · norm_num [mixed_004_243]
  · norm_num [mixed_004_243, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_243, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_243, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_243, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_243]

def mixed_004_244 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(77/1280), (39/640)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(15557119/100000000), (7835801/50000000), (349273/4000000), (14204261/100000000), (14204261/100000000), (16013979/100000000), (15616953/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1890801/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(348121/6250000), (3083/100000000), (4533081/100000000), (2106531/50000000), (1/100000000), (5408819/100000000), (124087/25000000)]
    alternative := .zero
    polynomial := [(-3286384137791296802271398394432347391095906089/1129474738224130559655951127034100000000000000), (148640874327/1541500000), (-452728626921998974783292555297431130123014031089/564737369112065279827975563517050000000000000), (148640874327/1541500000), (-902170869706206652764313712200429912854932156089/1129474738224130559655951127034100000000000000)]
    bernstein := [(49494637557334505293894931012275233840321298462098019/104548643584715557580958773758314676224000000000000000000), (28090458126941639816361285034871107949068432208557033/52274321792357778790479386879157338112000000000000000000), (1181937462181185632472804188626530473324891911894686797/2273932997967563377385853329243344207872000000000000000000), (159415001015297863051031932125571589738954865614330893/378988832994593896230975554873890701312000000000000000000), (45463826822308539719800042714153134214504135409582951/189494416497296948115487777436945350656000000000000000000)]
    reserve := (119960861/500000000000) }

theorem mixed_004_244_valid : mixed_004_244.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_244]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_244]
  · intro i; fin_cases i <;> norm_num [mixed_004_244]
  · norm_num [mixed_004_244]
  · norm_num [mixed_004_244, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_244, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_244, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_244, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_244]

def mixed_004_245 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(39/640), (79/1280)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(15570807/100000000), (15688377/100000000), (8735093/100000000), (7100053/50000000), (7100053/50000000), (16003011/100000000), (7801249/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1917067/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(21757/390625), (1543/50000000), (2268593/50000000), (21063/500000), (1/100000000), (108121/2000000), (251109/50000000)]
    alternative := .zero
    polynomial := [(-69415231717534265029446326577280738568199667/23228053278627854420539504747200000000000000), (6034393689583/61720000000), (-9320553935269054214069611331209181205788199667/11614026639313927210269752373600000000000000), (6034393689583/61720000000), (-18571692638820574163109776335841081673008199667/23228053278627854420539504747200000000000000)]
    bernstein := [(1883211535232313461979498246854628550725339162521453/3897020671150476972299461076767997952000000000000000000), (4265958741231321379850041326533061856234494568471333/7794041342300953944598922153535995904000000000000000000), (3539364550389374538997427501070514047820148153244977/6680606864829389095370504703030853632000000000000000000), (13424930159367710038662347372466778682671058104158293/31176165369203815778395688614143983616000000000000000000), (15574303037129336068398026309393029530256894834087373/62352330738407631556791377228287967232000000000000000000)]
    reserve := (249779003/1000000000000) }

theorem mixed_004_245_valid : mixed_004_245.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_245]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_245]
  · intro i; fin_cases i <;> norm_num [mixed_004_245]
  · norm_num [mixed_004_245]
  · norm_num [mixed_004_245, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_245, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_245, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_245, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_245]

def mixed_004_246 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(79/1280), (1/16)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(15584491/100000000), (15705193/100000000), (8738361/100000000), (14195937/100000000), (14195937/100000000), (15992021/100000000), (15588059/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1943383/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2784827/50000000), (3089/100000000), (4541301/100000000), (526517/12500000), (1/100000000), (5403273/100000000), (127019/25000000)]
    alternative := .zero
    polynomial := [(-1443828394862314803326569737301762456455075250259/470557999518400145189804100302817900000000000000), (30617508116421/308900000000), (-189021925817304376679870593373862801931562871625259/235278999759200072594902050151408950000000000000), (30617508116421/308900000000), (-376600023239746438556414617010423841406670668000259/470557999518400145189804100302817900000000000000)]
    bernstein := [(622940408379713228461293015425295221474532282632011109821/1263144511751695233644912702154566610714624000000000000000000), (2933650308978747568137121131841232084687927899170283793/5263102132298730140187136258977360877977600000000000000000), (319682043161187502660630112504635273184242810627415959/592098989883607140771052829134953098772480000000000000000), (362410439954400719209549386175720048935677919843761/822359708171676584404240040465212637184000000000000000), (8009841363684062059846452718065504231067730893309/30838489056437871915159001517445473894400000000000000)]
    reserve := (259735207/1000000000000) }

theorem mixed_004_246_valid : mixed_004_246.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_246]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_246]
  · intro i; fin_cases i <;> norm_num [mixed_004_246]
  · norm_num [mixed_004_246]
  · norm_num [mixed_004_246, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_246, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_246, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_246, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_246]

def mixed_004_247 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/16), (81/1280)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(7829783/50000000), (3945983/25000000), (8752591/100000000), (14172519/100000000), (14172519/100000000), (3983271/25000000), (15525789/100000000)]
    cone := fun i => (![![0, 0, 0, (8361/12500000), 0], ![(1977501/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2785971/50000000), (97/3125000), (4560439/100000000), (2104493/50000000), (1/100000000), (5388211/100000000), (25621/5000000)]
    alternative := .zero
    polynomial := [(-226427511824455278451257168377214591184854167867/71609910101979483271490686681663800000000000000), (7827281353011/77600000000), (-28910533559885954640338830706360197286873348117867/35804955050989741635745343340831900000000000000), (7827281353011/77600000000), (-57594639607947454002226404244343179982561842067867/71609910101979483271490686681663800000000000000)]
    bernstein := [(2358743468641204518067335161543437807529292252517/4693027068443327415680413642369518796800000000000000), (213117872031548340338831708539971686290127242959541/375442165475466193254433091389561503744000000000000000), (49608177358015167406063677370184732203221285109875727/90106119714111886381063941933494760898560000000000000000), (1084438999255330313366040547327683608551259795810507093/2402829859042983636828371784893193623961600000000000000000), (51887021429539213485953193453132739117771485609154544293/192226388723438690946269742791455489916928000000000000000000)]
    reserve := (26992663/100000000000) }

theorem mixed_004_247_valid : mixed_004_247.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_247]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_247]
  · intro i; fin_cases i <;> norm_num [mixed_004_247]
  · norm_num [mixed_004_247]
  · norm_num [mixed_004_247, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_247, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_247, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_247, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_247]

def mixed_004_248 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(81/1280), (41/640)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(393593/2500000), (15871893/100000000), (8768279/100000000), (14146161/100000000), (14146161/100000000), (7933591/50000000), (3091321/20000000)]
    cone := fun i => (![![0, 0, 0, (143557/100000000), 0], ![(80521/4000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5574617/100000000), (3121/100000000), (916361/20000000), (131419/3125000), (1/100000000), (1074269/20000000), (258247/50000000)]
    alternative := .zero
    polynomial := [(-568320398600227300975254681218575352321158405939/174382597597349976745568226554762700000000000000), (6409399506947/62420000000), (-70791991152906047676168938917204099501473545905939/87191298798674988372784113277381350000000000000), (6409399506947/62420000000), (-12819605627928351641032965741199056695511448491449/15852963417940906976869838777705700000000000000)]
    bernstein := [(240548152194984256729037506606449553157884601582447656781/468104721045091453992860028743390343462912000000000000000000), (19386818230165778512923087652322904320560922209352497363/33436051503220818142347144910242167390208000000000000000000), (197717948592252868924384805271656018066023647346286813303/351078540783818590494645021557542757597184000000000000000000), (352545273577740685364368276337247911315081611715233993/759910261436836775962435111596412895232000000000000000000), (485446665574145331343795372363017075573806264747797213/1720973239136365639679632458615405674496000000000000000000)]
    reserve := (35259603/125000000000) }

theorem mixed_004_248_valid : mixed_004_248.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_248]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_248]
  · intro i; fin_cases i <;> norm_num [mixed_004_248]
  · norm_num [mixed_004_248]
  · norm_num [mixed_004_248, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_248, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_248, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_248, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_248]

def mixed_004_249 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(41/640), (83/1280)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(1976629/12500000), (15944961/100000000), (1097653/12500000), (14124423/100000000), (14124423/100000000), (1976629/12500000), (3079781/20000000)]
    cone := fun i => (![![0, 0, 0, (207063/100000000), 0], ![(1023451/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5576691/100000000), (627/20000000), (4599551/100000000), (2101233/50000000), (1/100000000), (5357479/100000000), (520901/100000000)]
    alternative := .zero
    polynomial := [(-424991291077481829872433278742168584877848891/126676602496558630690312796831456250000000000), (247987300721/2375000000), (-51662077458678197342981457994201490469551648891/63338301248279315345156398415728125000000000), (247987300721/2375000000), (-102899163626278912856090482709660812354225448891/126676602496558630690312796831456250000000000)]
    bernstein := [(11210326554844443265938142936913018130168348522155749/21252807222309034037556069000054571008000000000000000000), (8418509827218840484221813555137866922781599411132429/14168538148206022691704046000036380672000000000000000000), (147383343488471808992719054807058068065697499506387543/255033686667708408450672828000654852096000000000000000000), (27126947698134928427292415777197304725972684773949701/56674152592824090766816184000145522688000000000000000000), (100791612483797778264636498408414993741292051412464789/340044915556944544600897104000873136128000000000000000000)]
    reserve := (148203381/500000000000) }

theorem mixed_004_249_valid : mixed_004_249.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_249]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_249]
  · intro i; fin_cases i <;> norm_num [mixed_004_249]
  · norm_num [mixed_004_249]
  · norm_num [mixed_004_249, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_249, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_249, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_249, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_249]

def mixed_004_250 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(83/1280), (21/320)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(634231/4000000), (15991301/100000000), (1757897/20000000), (3527771/25000000), (3527771/25000000), (15779733/100000000), (7680769/50000000)]
    cone := fun i => (![![0, 0, 0, (247119/100000000), 0], ![(519381/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1394413/25000000), (393/12500000), (4610817/100000000), (4200707/100000000), (1/100000000), (33431/625000), (262979/50000000)]
    alternative := .zero
    polynomial := [(-857634270903891538328846303893714285146133777/248841848630137532944768879779144000000000000), (21195232169/200000000), (-101772921971737891937667483265053323485302868777/124420924315068766472384439889572000000000000), (21195232169/200000000), (-202688209672571892337006120226212932685459603777/248841848630137532944768879779144000000000000)]
    bernstein := [(362370319525264400260604497656545268794994997515371183/667979751089139439987440570581236989296640000000000000000), (231904493428546229929038338469287647733020866809839/380398491508621548967790757734189629440000000000000000), (74343975160576147215942225772678578715648865528228381/125246203329213644997645106983981935493120000000000000000), (11752301623316718367519790570738680535480088261791/23774905719288846810486922358386851840000000000000000), (813633203613375048024458490319501160419693077371663/2609295902691950937450939728832956989440000000000000000)]
    reserve := (311820979/1000000000000) }

theorem mixed_004_250_valid : mixed_004_250.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_250]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_250]
  · intro i; fin_cases i <;> norm_num [mixed_004_250]
  · norm_num [mixed_004_250]
  · norm_num [mixed_004_250, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_250, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_250, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_250, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_250]

def mixed_004_251 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(21/320), (17/256)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(199253/1250000), (3215957/20000000), (275151/3125000), (7042193/50000000), (7042193/50000000), (1571387/10000000), (15292501/100000000)]
    cone := fun i => (![![0, 0, 0, (32387/10000000), 0], ![(1056911/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(697551/12500000), (3161/100000000), (1158071/25000000), (4197037/100000000), (1/100000000), (5332061/100000000), (529889/100000000)]
    alternative := .zero
    polynomial := [(-358229310469871792616534188908442381186259134839/100933934824648318039477457519511710000000000000), (4260810309949/39512500000), (-41509186735326794524829527220203938223787425634839/50466967412324159019738728759755855000000000000), (4260810309949/39512500000), (-82660144160183717257042520251499434066388592134839/100933934824648318039477457519511710000000000000)]
    bernstein := [(590977126088733711999851663038330121593925474428741241/1058369016426904347365631144959795108249600000000000000000), (40800790370521785737202412898249274216131751652375929/65130401010886421376346531997525852815360000000000000000), (1241285726422110464646427382401614947316671283008838563/2032068511539656346942011798322806607839232000000000000000), (852966833860686228834443086112694555925345964282377/1667338265878692387234471219136661832073216000000000000), (227929051387853315165734317820146339397353497675929/693612718605536033089540027160851322142457856000000000)]
    reserve := (328611407/1000000000000) }

theorem mixed_004_251_valid : mixed_004_251.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_251]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_251]
  · intro i; fin_cases i <;> norm_num [mixed_004_251]
  · norm_num [mixed_004_251]
  · norm_num [mixed_004_251, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_251, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_251, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_251, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_251]

def mixed_004_252 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(17/256), (43/640)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(801243/5000000), (16168501/100000000), (137813/1562500), (7028769/50000000), (7028769/50000000), (7824009/50000000), (7611757/50000000)]
    cone := fun i => (![![0, 0, 0, (400673/100000000), 0], ![(134401/6250000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2791601/50000000), (1589/50000000), (1163449/25000000), (2096663/50000000), (1/100000000), (2657573/50000000), (106753/20000000)]
    alternative := .zero
    polynomial := [(-12017862336348347198767150870763810666984840417/3289135302523429146145591758597607500000000000), (174328819507/1589000000), (-1360150887360434591667199585159975365726633995417/1644567651261714573072795879298803750000000000), (174328819507/1589000000), (-2708283912384520836135632019449186920786283150417/3289135302523429146145591758597607500000000000)]
    bernstein := [(13026593236165195832832401760539968573090684049887/22602765690331511130349633692390161658150912000000000), (43409960074296841518927250145161684604718614243689/67270135983129497411754862179732623982592000000000000), (166915221058228822628443125169306061424891271925672581/264876160433572396058784769832697206931456000000000000000), (39060404811653859212945341109623420013976637201950319/73576711231547887794106880509082557480960000000000000000), (191728965362061730452559496976560566634833419154256383/551825334236609158455801603818119181107200000000000000000)]
    reserve := (347445021/1000000000000) }

theorem mixed_004_252_valid : mixed_004_252.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_252]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_252]
  · intro i; fin_cases i <;> norm_num [mixed_004_252]
  · norm_num [mixed_004_252]
  · norm_num [mixed_004_252, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_252, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_252, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_252, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_252]

def mixed_004_253 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(43/640), (11/160)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(4038019/25000000), (3260401/20000000), (4421277/50000000), (2803397/20000000), (2803397/20000000), (971829/6250000), (15120131/100000000)]
    cone := fun i => (![![0, 0, 0, (128993/25000000), 0], ![(2205863/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(279373/5000000), (6407/100000000), (4686149/100000000), (4187683/100000000), (1/100000000), (5289743/100000000), (67803/12500000)]
    alternative := .zero
    polynomial := [(-1201533087840714969498082929982683600832360367299/629915847427299642632085054886663650000000000000), (36153739013949/640700000000), (-132006286039576179825886319619037820353156619867299/314957923713649821316042527443331825000000000000), (36153739013949/640700000000), (-262811038991311644682274556308092957105480879367299/629915847427299642632085054886663650000000000000)]
    bernstein := [(48752934363670048730729149317096109559354782490553832301/105682342341108504011612994962054115753984000000000000000000), (5324580765410750064479821333204091235278984606107846959/8806861861759042000967749580171176312832000000000000000000), (11440670656595530629669315044466391650135541815727962887/19815439188957844502177436555385146703872000000000000000000), (2153841477266490067434545634372051926522578279069263/5674524395463300258355508750110294016000000000000000000), (4600754860915730339232119364843004511593853499970541/412821649769955093795363261570523889664000000000000000000)]
    reserve := (5572327/500000000000) }

theorem mixed_004_253_valid : mixed_004_253.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_253]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_253]
  · intro i; fin_cases i <;> norm_num [mixed_004_253]
  · norm_num [mixed_004_253]
  · norm_num [mixed_004_253, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_253, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_253, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_253, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_253]

def mixed_004_254 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(11/160), (9/128)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(16322219/100000000), (16480809/100000000), (4436031/50000000), (6981197/50000000), (6981197/50000000), (3854411/25000000), (14982479/100000000)]
    cone := fun i => (![![0, 0, 0, (66987/10000000), 0], ![(570209/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1118653/20000000), (1619/25000000), (2364721/50000000), (4180017/100000000), (1/100000000), (2627909/50000000), (137457/25000000)]
    alternative := .zero
    polynomial := [(-2543740119562019940646056380527904134110183181/1260549820701498070120251327489900000000000000), (9446018886083/161900000000), (-2402986052336195306989799578160427690934442523629/5672474193156741315541130973704550000000000000), (9446018886083/161900000000), (-4783078443596332434513784648896104244661893398629/11344948386313482631082261947409100000000000000)]
    bernstein := [(3761776562669845803474107079479360237871298382852011/7435025374454403977106071189854027776000000000000000000), (3883100608300863279071900577087751612982005200781289/5948020299563523181684856951883222220800000000000000000), (8956062491025439103877826776388247489111070699530137/14275248718952455636043656684519733329920000000000000000), (12111980207184842678186006726968178201033747728631/28198022160893739527987469994113053491200000000000000), (801662994650575041409331254839232502100799546331/13535050637228994973433985597174265675776000000000000)]
    reserve := (29614333/500000000000) }

theorem mixed_004_254_valid : mixed_004_254.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_254]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_254]
  · intro i; fin_cases i <;> norm_num [mixed_004_254]
  · norm_num [mixed_004_254]
  · norm_num [mixed_004_254, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_254, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_254, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_254, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_254]

def mixed_004_255 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(9/128), (23/320)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(16492943/100000000), (16660511/100000000), (2225241/25000000), (13907213/100000000), (13907213/100000000), (15286099/100000000), (14845057/100000000)]
    cone := fun i => (![![0, 0, 0, (823943/100000000), 0], ![(2357003/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1119843/20000000), (1309/20000000), (4772909/100000000), (1043047/25000000), (1/100000000), (1044367/20000000), (557019/100000000)]
    alternative := .zero
    polynomial := [(-1972507024493558662249220924223779112609376121/924898942565790053327764979534700000000000000), (512509041619/8500000000), (-10098414820148468556182071130300730449573513582171/23584923035427646359858006978134850000000000000), (512509041619/8500000000), (-20096231782047765620589431993466048164403948982171/47169846070855292719716013956269700000000000000)]
    bernstein := [(94340591558143591752731562178400100559619576554607/168827455193064650816405978624714946379776000000000000), (213840999902570041269067327794471855859638886088419/301477598559044019315010676115562404249600000000000000), (162777822214942600493474114915248381056003293271704527/237413608865247165210570907441005393346560000000000000000), (13784176558330288857737171403875246480193817904030221/28263524864910376810782250885833975398400000000000000000), (57111435411968427752997865072852908256135523906921989/494611685135931594188689390502094569472000000000000000000)]
    reserve := (57733609/500000000000) }

theorem mixed_004_255_valid : mixed_004_255.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_255]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_255]
  · intro i; fin_cases i <;> norm_num [mixed_004_255]
  · norm_num [mixed_004_255]
  · norm_num [mixed_004_255, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_255, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_255, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_255, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_255]

def mixed_004_256 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(23/320), (47/640)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(16664227/100000000), (168411/1000000), (1116157/12500000), (1731431/12500000), (1731431/12500000), (7577321/50000000), (367697/2500000)]
    cone := fun i => (![![0, 0, 0, (489087/50000000), 0], ![(2434371/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5605309/100000000), (1323/20000000), (4816549/100000000), (1041049/25000000), (1/100000000), (5187797/100000000), (281999/50000000)]
    alternative := .zero
    polynomial := [(-12247247854012344763870253101924363479797870632667/5439977443526246921934569718843272100000000000000), (9153793489/147000000), (-168137475270580757196192676196611551607064360090381/388569817394731922995326408488805150000000000000), (9153793489/147000000), (-2341677405934118255982827213650637359019103170632667/5439977443526246921934569718843272100000000000000)]
    bernstein := [(35355020941884876536289296045747709943709003794025267653/57042297878229778924144633775058028855296000000000000000000), (4204527280350569855195358176943010448501374624233597977/5432599797926645611823298454767431319552000000000000000000), (514783252554647502058192608434892206415466046741984335039/684507574538757347089735605300696346263552000000000000000000), (84279679837903029560196103538815176528648244590793189919/152112794341946077131052356733488076947456000000000000000000), (164205951320511676971561592798952597020050163920564803173/912676766051676462786314140400928461684736000000000000000000)]
    reserve := (89958437/500000000000) }

theorem mixed_004_256_valid : mixed_004_256.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_256]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_256]
  · intro i; fin_cases i <;> norm_num [mixed_004_256]
  · norm_num [mixed_004_256]
  · norm_num [mixed_004_256, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_256, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_256, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_256, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_256]

def mixed_004_257 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(47/640), (3/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(8418027/50000000), (8511281/50000000), (34988/390625), (431097/3125000), (431097/3125000), (1877911/12500000), (182137/1250000)]
    cone := fun i => (![![0, 0, 0, (1132547/100000000), 0], ![(157059/6250000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2805773/50000000), (1337/20000000), (4860359/100000000), (4156041/100000000), (1/100000000), (2576853/50000000), (285383/50000000)]
    alternative := .zero
    polynomial := [(-45003927549374978772106686220801939034264806921/18954071906460774334225342463406150000000000000), (47959328993/746093750), (-4144252886235824186505643637015706883341999406921/9477035953230387167112671231703075000000000000), (47959328993/746093750), (-8243501844922273394239180587810611827649734006921/18954071906460774334225342463406150000000000000)]
    bernstein := [(2191000709876395533552323297788386555247310709268178999/3179965584542242065325547631825370742784000000000000000000), (168301106354409313198770395690817271013166125283379051/198747849033890129082846726989085671424000000000000000000), (30807662689684361740604597278691742911494822442207597/37265221693854399203033761310453563392000000000000000000), (488065612645093554861606080004618528421444617081251/776358785288633316729870027301115904000000000000000000), (12255944118694689644753845143872506377488604354599/48522424080539582295616876706319744000000000000000000)]
    reserve := (31572887/125000000000) }

theorem mixed_004_257_valid : mixed_004_257.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_257]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_257]
  · intro i; fin_cases i <;> norm_num [mixed_004_257]
  · norm_num [mixed_004_257]
  · norm_num [mixed_004_257, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_257, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_257, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_257, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_257]

def mixed_004_258 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/40), (49/640)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(4252101/25000000), (4301221/25000000), (359359/4000000), (13738189/100000000), (13738189/100000000), (14892051/100000000), (1443431/10000000)]
    cone := fun i => (![![0, 0, 0, (1287047/100000000), 0], ![(1296363/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(224717/4000000), (1351/20000000), (980867/20000000), (4147723/100000000), (1/100000000), (319973/6250000), (577323/100000000)]
    alternative := .zero
    polynomial := [(-28541243173171448050920803814212995726410100651/11408100620243627721217613153560650000000000000), (11200639400471/168875000000), (-2520782501556672107088663256857504952580596000651/5704050310121813860608806576780325000000000000), (11200639400471/168875000000), (-5013023759940172766126405709900796909434781900651/11408100620243627721217613153560650000000000000)]
    bernstein := [(22382249644917742501310816517551724788764516738469/29204737587823686966317089673115264000000000000000000), (433583660886865257221937277640086917403139037373127/467275801405178991461073434769844224000000000000000000), (20402055744195842619594932433196817271272345676316823/22429238467448591590131524868952522752000000000000000000), (85110862246455476256548644666233793189854897425574703/119622605159725821814034799301080121344000000000000000000), (638229216962190320772056411997396639438921633529675349/1913961682555613149024556788817281941504000000000000000000)]
    reserve := (333459767/1000000000000) }

theorem mixed_004_258_valid : mixed_004_258.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_258]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_258]
  · intro i; fin_cases i <;> norm_num [mixed_004_258]
  · norm_num [mixed_004_258]
  · norm_num [mixed_004_258, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_258, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_258, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_258, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_258]

def mixed_004_259 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(49/640), (5/64)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(2147657/12500000), (4347013/25000000), (2252597/25000000), (13680707/100000000), (13680707/100000000), (7380473/50000000), (1787243/12500000)]
    cone := fun i => (![![0, 0, 0, (180207/12500000), 0], ![(66843/2500000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1406111/25000000), (273/4000000), (197939/4000000), (4139241/100000000), (1/100000000), (635673/12500000), (583671/100000000)]
    alternative := .zero
    polynomial := [(-72145864334462444772774825874196559338401/27391795641152991686617400850000000000000), (27789255553/406250000), (-14272373257114818553199698252343317343576269/31957094914678490301053634325000000000000), (27789255553/406250000), (-85129218492347674205788765732940528146088807/191742569488070941806321805950000000000000)]
    bernstein := [(1305103450198708552170101724201723977552983092533/1531860240331607435241948144730112000000000000000000), (93492984624879289885147868316934851014982705359/91911614419896446114516888683806720000000000000000), (321932166424891040583872524414028372495468818001/321690650469637561400809110393323520000000000000000), (224496658757091432830362404150169086545929351/279731000408380488174616617733324800000000000000), (34851497601966842686163756172737464783797967/82484782171701938820720284716236800000000000000)]
    reserve := (105630083/250000000000) }

theorem mixed_004_259_valid : mixed_004_259.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_259]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_259]
  · intro i; fin_cases i <;> norm_num [mixed_004_259]
  · norm_num [mixed_004_259]
  · norm_num [mixed_004_259, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_259, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_259, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_259, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_259]

def mixed_004_260 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(5/64), (51/640)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(17354593/100000000), (17572053/100000000), (9036163/100000000), (2724533/20000000), (2724533/20000000), (14629987/100000000), (3540469/25000000)]
    cone := fun i => (![![0, 0, 0, (798179/50000000), 0], ![(2755931/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5631103/100000000), (431/6250000), (624097/12500000), (2065299/50000000), (1/100000000), (2525579/50000000), (589811/100000000)]
    alternative := .zero
    polynomial := [(-107570143334237509700771990780522475315397583339/38832768227793701902791546890840425000000000000), (9724537238027/137920000000), (-17524229890446130707168001070260730466052539338553/38832768227793701902791546890840425000000000000), (9724537238027/137920000000), (-8708329873555946598733614539740103995368570877607/19416384113896850951395773445420212500000000000)]
    bernstein := [(308083248831764359959054849247397776752051651879913/325752870217816070131372392580879115878400000000000000), (726241420326331032707218395771865911927569814016379/651505740435632140262744785161758231756800000000000000), (35835548429876919107360724612641694775004208445397001/32575287021781607013137239258087911587840000000000000000), (58753186784438816139455586273010291248630919071198299/65150574043563214026274478516175823175680000000000000000), (1693295508840715262081903176365842115650543139959031593/3257528702178160701313723925808791158784000000000000000000)]
    reserve := (10396197/20000000000) }

theorem mixed_004_260_valid : mixed_004_260.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_260]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_260]
  · intro i; fin_cases i <;> norm_num [mixed_004_260]
  · norm_num [mixed_004_260]
  · norm_num [mixed_004_260, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_260, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_260, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_260, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_260]

def mixed_004_261 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(51/640), (13/160)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(2191049/12500000), (2219609/12500000), (9061291/100000000), (13564069/100000000), (13564069/100000000), (14499189/100000000), (7013059/50000000)]
    cone := fun i => (![![0, 0, 0, (1751137/100000000), 0], ![(2839361/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5637899/100000000), (3483/50000000), (1007447/20000000), (4121791/100000000), (1/100000000), (2508447/50000000), (18617/3125000)]
    alternative := .zero
    polynomial := [(-17188582257474012863471431137451586035507871111/5903830142289187248095846092855800000000000000), (3163348857173/43537500000), (-448739086532987133906456311680173388171161644537/983971690381531208015974348809300000000000000), (3163348857173/43537500000), (-2675245936940448790575266438943588742991461996111/5903830142289187248095846092855800000000000000)]
    bernstein := [(1037784847025420739184409947472856254868698753782855489/990498335244964289257495986025978134528000000000000000000), (302221183816716447891482254410084476384545646924097407/247624583811241072314373996506494533632000000000000000000), (74763963550201823977647991751934918505675167389730241/61906145952810268078593499126623633408000000000000000000), (15620829496810196252242466433707252725347203410608383/15476536488202567019648374781655908352000000000000000000), (2419309645156799317774920885411566190778736754852929/3869134122050641754912093695413977088000000000000000000)]
    reserve := (19540141/31250000000) }

theorem mixed_004_261_valid : mixed_004_261.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_261]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_261]
  · intro i; fin_cases i <;> norm_num [mixed_004_261]
  · norm_num [mixed_004_261]
  · norm_num [mixed_004_261, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_261, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_261, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_261, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_261]

def mixed_004_262 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(13/160), (27/320)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(4447479/25000000), (4508901/25000000), (9097757/100000000), (6737577/50000000), (6737577/50000000), (3575831/25000000), (13823091/100000000)]
    cone := fun i => (![![0, 0, 0, (495853/25000000), 0], ![(2966801/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5648351/100000000), (14147/100000000), (1276053/25000000), (4108277/100000000), (1/100000000), (993087/20000000), (15241/2500000)]
    alternative := .zero
    polynomial := [(-3847879739718400107044405215611611004938436463/2457511253914761087568033647590550000000000000), (26949579259779/707350000000), (-40930414778847223844092666102449512203688030209/175536518136768649112002403399325000000000000), (26949579259779/707350000000), (-569177927164142733710252920218681559846693986463/2457511253914761087568033647590550000000000000)]
    bernstein := [(1359764229676626821704989553257266415056373153903857/1610554575365577826348586531284942848000000000000000000), (3893064188052847507027408428302987441639392004662103/3221109150731155652697173062569885696000000000000000000), (23068420300778278767206303641118740540658629584509411/19326654904386933916183038375419314176000000000000000000), (10294530053099002442828848013218457579758630402480423/12884436602924622610788692250279542784000000000000000000), (630135183503716339843881577456853122798733536507217/25768873205849245221577384500559085568000000000000000000)]
    reserve := (12226673/500000000000) }

theorem mixed_004_262_valid : mixed_004_262.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_262]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_262]
  · intro i; fin_cases i <;> norm_num [mixed_004_262]
  · norm_num [mixed_004_262]
  · norm_num [mixed_004_262, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_262, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_262, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_262, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_262]

def mixed_004_263 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(27/320), (7/80)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(4535011/25000000), (2301247/12500000), (9144059/100000000), (13354727/100000000), (13354727/100000000), (14042867/100000000), (13553599/100000000)]
    cone := fun i => (![![0, 0, 0, (2293223/100000000), 0], ![(3141017/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5662759/100000000), (14433/100000000), (129851/2500000), (4089691/100000000), (1/100000000), (61209/1250000), (310087/50000000)]
    alternative := .zero
    polynomial := [(-11814136571705996138349498151901174149838162017/6864961129412984712044874684378675000000000000), (102857395361/2550000000), (-816572468494171814460212266323622913531579724517/3432480564706492356022437342189337500000000000), (102857395361/2550000000), (-95372400024508096046004413793843803112548311001/403821242906646159532051452022275000000000000)]
    bernstein := [(77958593150588044593452265219233909863136473679992103/71984334812353498574171665170470535168000000000000000000), (26313362709021591264678886169257516853132280900758723/17996083703088374643542916292617633792000000000000000000), (19629422802331304099335581812272214129842930580811629/13497062777316280982657187219463225344000000000000000000), (1191365345031430251485012006602221651106603455767563/1124755231443023415221432268288602112000000000000000000), (77740576235943016426568699653553730354077396489783/281188807860755853805358067072150528000000000000000000)]
    reserve := (27647109/100000000000) }

theorem mixed_004_263_valid : mixed_004_263.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_263]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_263]
  · intro i; fin_cases i <;> norm_num [mixed_004_263]
  · norm_num [mixed_004_263]
  · norm_num [mixed_004_263, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_263, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_263, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_263, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_263]

def mixed_004_264 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(7/80), (29/320)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(9245827/50000000), (4696839/25000000), (1837533/20000000), (6616107/50000000), (6616107/50000000), (861457/6250000), (2657117/20000000)]
    cone := fun i => (![![0, 0, 0, (1301517/50000000), 0], ![(1660081/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1135539/20000000), (14721/100000000), (1321111/25000000), (203523/5000000), (1/100000000), (1206979/25000000), (629903/100000000)]
    alternative := .zero
    polynomial := [(-35804081710536218261963198957744745166047219877/18984233076555258093055608655532550000000000000), (1494481420601/35050000000), (-2303497448164926484763985030293031752756193219877/9492116538277629046527804327766275000000000000), (1494481420601/35050000000), (-4571190814619316751266006861628318760346339219877/18984233076555258093055608655532550000000000000)]
    bernstein := [(1053100871149536281082455343512304544180229304300923/777594186815703371491557730530613248000000000000000000), (604281269050984589662843011934778792551079394921809/345597416362534831774025658013605888000000000000000000), (65241510236281358462730118942483988702961457064131721/37324520967153761831594771065469435904000000000000000000), (7477686593225159441728157733312531039152499085669481/5529558661800557308384410528217694208000000000000000000), (111724191551792076110821372989235577551981119943781963/199064111824820063101838779015836991488000000000000000000)]
    reserve := (561247281/1000000000000) }

theorem mixed_004_264_valid : mixed_004_264.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_264]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_264]
  · intro i; fin_cases i <;> norm_num [mixed_004_264]
  · norm_num [mixed_004_264]
  · norm_num [mixed_004_264, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_264, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_264, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_264, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_264]

def mixed_004_265 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(29/320), (3/32)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(18844573/100000000), (19167621/100000000), (2307133/25000000), (6553837/50000000), (6553837/50000000), (13524771/100000000), (6509577/50000000)]
    cone := fun i => (![![0, 0, 0, (291271/10000000), 0], ![(3504249/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1423287/25000000), (1501/10000000), (2687699/50000000), (4050587/100000000), (1/100000000), (4759049/100000000), (15971/2500000)]
    alternative := .zero
    polynomial := [(-364402891013440039340831329187217393678905560327/176776306313533628662317782227464900000000000000), (67558951724709/1501000000000), (-21878043051425807624157207502445013522283458235327/88388153156766814331158891113732450000000000000), (67558951724709/1501000000000), (-43391683211838175208973583675702809650888010910327/176776306313533628662317782227464900000000000000)]
    bernstein := [(3073703306292071485387281180002405698125524536888055513/1853633921690198382082185308169462349824000000000000000000), (20171686539847688110622247001171013197747300359542269/9755968008895780958327291095628749209600000000000000000), (16479399231357316852952190162645889465947165709516829/7944145378672278780352222749297695784960000000000000000), (3110799607868795581190975300710964341061316701422343/1853633921690198382082185308169462349824000000000000000), (162877457988389837114125254244350074127200766071897/185363392169019838208218530816946234982400000000000000)]
    reserve := (878692691/1000000000000) }

theorem mixed_004_265_valid : mixed_004_265.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_265]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_265]
  · intro i; fin_cases i <;> norm_num [mixed_004_265]
  · norm_num [mixed_004_265]
  · norm_num [mixed_004_265, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_265, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_265, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_265, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_265]

def mixed_004_266 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/32), (31/320)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(19198629/100000000), (9775323/50000000), (1158327/12500000), (3245293/25000000), (3245293/25000000), (13267359/100000000), (1594301/12500000)]
    cone := fun i => (![![0, 0, 0, (322211/10000000), 0], ![(369329/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1141821/20000000), (15301/100000000), (1366719/25000000), (1007519/25000000), (1/100000000), (93803/2000000), (129399/20000000)]
    alternative := .zero
    polynomial := [(-7291438033630464573386203434560911869578027417/3244557364753530133316769194877300000000000000), (18149128939739/382525000000), (-409492158948814413577802603395633296247243427417/1622278682376765066658384597438650000000000000), (18149128939739/382525000000), (-811692879863998362582219003356705680624908827417/3244557364753530133316769194877300000000000000)]
    bernstein := [(6786182847056057338987798311035739700204638020887/3402164983303797613072764575287659724800000000000000), (82313540828341806071026080612269798534297936843587/34021649833037976130727645752876597248000000000000000), (2483889273850920546230611774684186682508535668333853/1020649494991139283921829372586297917440000000000000000), (6929809778244636945951610562199179082916855628667179/3402164983303797613072764575287659724800000000000000000), (3215850731502165806754294205449866711110141056659011/2617049987156767394671357365605892096000000000000000000)]
    reserve := (122880753/100000000000) }

theorem mixed_004_266_valid : mixed_004_266.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_266]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_266]
  · intro i; fin_cases i <;> norm_num [mixed_004_266]
  · norm_num [mixed_004_266]
  · norm_num [mixed_004_266, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_266, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_266, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_266, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_266]

def mixed_004_267 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(31/320), (1/10)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(4888411/25000000), (19936299/100000000), (232547/2500000), (12852771/100000000), (12852771/100000000), (6505593/50000000), (12491449/100000000)]
    cone := fun i => (![![0, 0, 0, (3531097/100000000), 0], ![(3887291/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5725553/100000000), (7797/50000000), (5558851/100000000), (4008931/100000000), (1/100000000), (924249/20000000), (654383/100000000)]
    alternative := .zero
    polynomial := [(-108447909457841466798693146040638002642713190243/44373112860078531733759291860957825000000000000), (25962592995807/519800000000), (-5709868522256507980718601129759013801185690190243/22186556430039265866879645930478912500000000000), (25962592995807/519800000000), (-11311289135055174494638509113477389599728667190243/44373112860078531733759291860957825000000000000)]
    bernstein := [(1099778434667183150590442087117865784248707531862403997/465285811903697064912583832223957123072000000000000000000), (13589887262902482980399461431814933374273179970421829/4846727207330177759506081585666220032000000000000000000), (3851677303328312879565304590821791416862936805786531/1363142027061612494861085445968624384000000000000000000), (11493277149232721144273748479715176005353707874689/4733132038408376718267657798502168000000000000000000), (715095818800491484475573486696824055164778581157/443731128600785317337592918609578250000000000000000)]
    reserve := (1611552069/1000000000000) }

theorem mixed_004_267_valid : mixed_004_267.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_267]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_267]
  · intro i; fin_cases i <;> norm_num [mixed_004_267]
  · norm_num [mixed_004_267]
  · norm_num [mixed_004_267, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_267, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_267, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_267, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_267]

def mixed_004_268 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/10), (17/160)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(26651463/100000000), (1361221/5000000), (6212289/50000000), (1684977/10000000), (1684977/10000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (13325731/100000000), 0], ![(111119/2000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (1684977/20000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(595233/12500000), (8511/20000000), (7561591/100000000), (16531/312500), (1/100000000), (1505289/50000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-19385889655296277842192865726239787792829/10591495321427018464802388300000000000000), (151257516299/4255500000), (-922320662506382081830586524983190825792829/5295747660713509232401194150000000000000), (151257516299/4255500000), (-1825255435357467885818980184240141863792829/10591495321427018464802388300000000000000)]
    bernstein := [(80527394704778818934826834691309049351371/105914953214270184648023883000000000000000000), (1390213483756176260335423507690880282182069/564879750476107651456127376000000000000000000), (246475574184535168315319562714245804195921557/81342684068559501809682342144000000000000000000), (356504478026401785130130780728348648255560241/144609216121883558772768608256000000000000000000), (5305870357362969969949599621657366346413541891/6941242373850410821092893196288000000000000000000)]
    reserve := (380151207/500000000000) }

theorem mixed_004_268_valid : mixed_004_268.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_268]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_268]
  · intro i; fin_cases i <;> norm_num [mixed_004_268]
  · norm_num [mixed_004_268]
  · norm_num [mixed_004_268, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_268, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_268, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_268, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_268]

def mixed_004_269 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(17/160), (9/80)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(3363977/12500000), (13781749/50000000), (2472779/20000000), (3316079/20000000), (3316079/20000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (3363977/25000000), 0], ![(5958237/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4145099/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(4808381/100000000), (4303/10000000), (763333/10000000), (5226113/100000000), (1/100000000), (185153/6250000), (1/100000000)]
    alternative := .zero
    polynomial := [(-244715537670033587007337345840614026692687/117557530198056439448349730700000000000000), (82114926816513/2151500000000), (-134906785193645786365586726385703647611804931/764123946287366856414273249550000000000000), (82114926816513/2151500000000), (-266632268397581136100078067275479312876604931/1528247892574733712828546499100000000000000)]
    bernstein := [(3965753451026552213117396466452037742007672377149/1001552538877777486039316233650176000000000000000000), (2847342472669444475607018621092789019720051189973/500776269438888743019658116825088000000000000000000), (1568670191706605199415185134902893222090162536621/250388134719444371509829058412544000000000000000000), (712942659173621673237348147875840453337662674117/125194067359722185754914529206272000000000000000000), (248675011916123423014584369911278507067572826909/62597033679861092877457264603136000000000000000000)]
    reserve := (494950751/125000000000) }

theorem mixed_004_269_valid : mixed_004_269.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_269]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_269]
  · intro i; fin_cases i <;> norm_num [mixed_004_269]
  · norm_num [mixed_004_269]
  · norm_num [mixed_004_269, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_269, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_269, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_269, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_269]

def mixed_004_270 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(9/80), (1/8)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(2729207/10000000), (14036401/50000000), (6134859/50000000), (3236541/20000000), (3236541/20000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (2729207/20000000), 0], ![(6574579/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (8091353/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2438161/50000000), (43749/50000000), (7741367/100000000), (2565747/50000000), (1/100000000), (22589/781250), (1/100000000)]
    alternative := .zero
    polynomial := [(-1058315966191378998221049926176683034107397/850817621115711714073440252960000000000000), (92283427250179/4374900000000), (-12769562053834803318878928380164924166035799/141802936852618619012240042160000000000000), (92283427250179/4374900000000), (-75559056356817440915052520354812861962107397/850817621115711714073440252960000000000000)]
    bernstein := [(183672405997833702360431723096688605759995038683/34849489760899551808448112761241600000000000000000), (928633443729604911110118323217198220918814179/105604514426968338813479129579520000000000000000), (3478411090953346144064687168549121137574385067/348494897608995518084481127612416000000000000000), (1863803228167941383304949979894862732782167/211209028853936677626958259159040000000000000), (740446626750886357625856386523179816329907/139397959043598207233792451044966400000000000)]
    reserve := (2635223747/500000000000) }

theorem mixed_004_270_valid : mixed_004_270.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_270]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_270]
  · intro i; fin_cases i <;> norm_num [mixed_004_270]
  · norm_num [mixed_004_270]
  · norm_num [mixed_004_270, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_270, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_270, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_270, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_270]

def mixed_004_271 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(14007077/50000000), (7273463/25000000), (12070847/100000000), (7705287/50000000), (7705287/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (14007077/100000000), 0], ![(7852351/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (7705287/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2502669/50000000), (180667/100000000), (7959049/100000000), (4946279/100000000), (1/100000000), (1376717/50000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-26859761820309394575082826889017378225172423/31417535013465939207724050054950000000000000), (57113784461513/4516675000000), (-735526445642331126994340655016649940919172423/15708767506732969603862025027475000000000000), (57113784461513/4516675000000), (-1444193129464352859413598483144282503613172423/31417535013465939207724050054950000000000000)]
    bernstein := [(3000766691511205242263867043564086350358501/395957610508173806137962181615616000000000000), (73796723257275448848719595570566270935695051/4949470131352172576724527270195200000000000000), (6000878330979247758271121224168722530079274453/344695241290597733021886720602880000000000000000), (30232677965211605940638058677132692731652075859/2010722240861820109294339203516800000000000000000), (38863180965196021649689487180295473959583908137/5026805602154550273235848008792000000000000000000)]
    reserve := (75785049/10000000000) }

theorem mixed_004_271_valid : mixed_004_271.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_271]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_271]
  · intro i; fin_cases i <;> norm_num [mixed_004_271]
  · norm_num [mixed_004_271]
  · norm_num [mixed_004_271, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_271, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_271, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_271, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_271]

def mixed_004_272 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(722327/2500000), (30460383/100000000), (11786541/100000000), (7214999/50000000), (7214999/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (722327/5000000), 0], ![(4822469/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (7214999/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5162377/100000000), (93913/50000000), (4126423/50000000), (4707907/100000000), (1/100000000), (2578233/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-5394688461773384378959431905174067367969139/4336218797577240498468629717073750000000000), (146894252745627/9391300000000), (-106985559079602379172401164878531635013344139/2168109398788620249234314858536875000000000), (146894252745627/9391300000000), (-208576429697431373965842897851889202658719139/4336218797577240498468629717073750000000000)]
    bernstein := [(14086452575165256952836768439166416977090458941/693795007612358479754980754731800000000000000000), (38965204223928071082145602765707818879229221829/1387590015224716959509961509463600000000000000000), (256223489235971910989526715115493116314423207303/8325540091348301757059769056781600000000000000000), (157269544468397271616539422939513071840503329269/5550360060898867838039846037854400000000000000000), (229663159392759617025406813170295287507870012061/11100720121797735676079692075708800000000000000000)]
    reserve := (20303479299/1000000000000) }

theorem mixed_004_272_valid : mixed_004_272.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_272]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_272]
  · intro i; fin_cases i <;> norm_num [mixed_004_272]
  · norm_num [mixed_004_272]
  · norm_num [mixed_004_272, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_272, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_272, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_272, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_272]

def mixed_004_273 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(29670857/100000000), (15916553/50000000), (11484259/100000000), (13505889/100000000), (13505889/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (14835429/100000000), 0], ![(11531993/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (422059/6250000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(165667/3125000), (194687/100000000), (534439/6250000), (223981/5000000), (1/100000000), (2413121/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-9663498055214138363546393786328360010336727/5590010611191051820736856738600000000000000), (183549577780129/9734350000000), (-145261968128439382018771230489868391248336727/2795005305595525910368428369300000000000000), (183549577780129/9734350000000), (-280860438201664625673996067193408422486336727/5590010611191051820736856738600000000000000)]
    bernstein := [(477378380605828243050484861834398711526365604873/14310427164649092661086353250816000000000000000000), (24813560440785721545106430779671975648435865213/596267798527045527545264718784000000000000000000), (7467116442573227790870504145983674492378584039/167700318335731554622105702158000000000000000000), (195791621057237838817065912221305883900955881/4658342175992543183947380615500000000000000000), (29734276258865069281766742161784845189093137/873439157998601846990133865406250000000000000)]
    reserve := (33358779239/1000000000000) }

theorem mixed_004_273_valid : mixed_004_273.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_273]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_273]
  · intro i; fin_cases i <;> norm_num [mixed_004_273]
  · norm_num [mixed_004_273]
  · norm_num [mixed_004_273, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_273, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_273, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_273, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_273]

def mixed_004_274 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(15171341/50000000), (166063/500000), (1116817/10000000), (6319137/50000000), (6319137/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (15171341/100000000), 0], ![(13505497/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (6319137/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(271069/5000000), (201237/100000000), (8853919/100000000), (4261641/100000000), (1/100000000), (2258103/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-59831461573289300253960596525735958567212689/25820897704101524776734118896450000000000000), (2242763348311/100618500000), (-706363941929769952928621149409037489667212689/12910448852050762388367059448225000000000000), (2242763348311/100618500000), (-450965474095416868534427234097446340255737563/8606965901367174925578039632150000000000000)]
    bernstein := [(62890868269924145327863841293114018530351853/1344838422088621082121568692523437500000000000), (3584747498407216080229185060962755735483123987/64552244260253811941835297241125000000000000000), (45458493953097853787241074621066626649679319537/774626931123045743302023566893500000000000000000), (154632264239313065053187949934193547564102728773/2754229088437495976184972682288000000000000000000), (3160509362838312328896588188458482636232304718671/66101498122499903428439344374912000000000000000000)]
    reserve := (46764627807/1000000000000) }

theorem mixed_004_274_valid : mixed_004_274.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_274]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_274]
  · intro i; fin_cases i <;> norm_num [mixed_004_274]
  · norm_num [mixed_004_274]
  · norm_num [mixed_004_274, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_274, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_274, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_274, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_274]

def mixed_004_275 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![(1824171/12500000), (42824877/100000000), (669751/5000000), (1824171/12500000), (1824171/12500000), 0, 0]
    cone := fun i => (![![0, 0, 0, (1824171/25000000), 0], ![(2043859/10000000), 0, (11829143/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (1824171/25000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2607423/100000000), (16049/6250000), (1417247/12500000), (1251329/25000000), (1/100000000), (2607423/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-8568269628560976604706500121778770969/2283458716012617534190800000000000000), (8246219434043889/256784000000000), (-81403508993516981686946187144595520969/1141729358006308767095400000000000000), (8246219434043889/256784000000000), (-154238748358472986769185874167412270969/2283458716012617534190800000000000000)]
    bernstein := [(8041458381674657836609489075209565545551/142576934463226850915328000000000000000000), (74393275536815698243725754759975348523/1096745649717129622425600000000000000000), (12618699952116383574534230794304403277669/175369629389769026625853440000000000000000), (30874343200094094620579853599964840851/449665716384023145194496000000000000000), (33793645802950744763178108186220589959/584565431299230088752844800000000000000)]
    reserve := (28200418293/500000000000) }

theorem mixed_004_275_valid : mixed_004_275.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_275]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_275]
  · intro i; fin_cases i <;> norm_num [mixed_004_275]
  · norm_num [mixed_004_275]
  · norm_num [mixed_004_275, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_275, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_275, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_275, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_275]

def mixed_004_276 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![0, (62809767/100000000), (18090947/100000000), (9549643/50000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(6717/20000), 0, (54711797/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(238741/25000000), 0, (9549643/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (37231/10000000), (660639/4000000), (3323643/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-36807774432254033047358479489463/5449943744189905800000000000000), (38752885272178701/744620000000000), (-288323697170480851780841553589463/2724971872094952900000000000000), (38752885272178701/744620000000000), (-539839619908707670514324627689463/5449943744189905800000000000000)]
    bernstein := [(98260394814416055009358004265193/1395185598512615884800000000000000), (406223111747073306293563905580353/4650618661708719616000000000000000), (39111159706768286411406579139945843/418555679553784765440000000000000000), (41171662566112174397423369569078089/465061866170871961600000000000000000), (1009901119780614063168161019984818617/13951855985126158848000000000000000000)]
    reserve := (70428188851/1000000000000) }

theorem mixed_004_276_valid : mixed_004_276.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_276]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_276]
  · intro i; fin_cases i <;> norm_num [mixed_004_276]
  · norm_num [mixed_004_276]
  · norm_num [mixed_004_276, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_276, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_276, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_276, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_276]

def mixed_004_277 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![0, (32515479/50000000), (8630393/50000000), (17708257/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(18646541/50000000), 0, (27550639/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(885413/100000000), 0, (17708257/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (95169/25000000), (17000989/100000000), (6248491/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-8477303153785041133256426976697117/1010985300099393923100000000000000), (3743400674107233/63446000000000), (-56059136513685939132448989236197117/505492650049696961550000000000000), (3743400674107233/63446000000000), (-103640969873586837131641551495697117/1010985300099393923100000000000000)]
    bernstein := [(243596674313727508843451522572617287603/2588122368254448443136000000000000000000), (72482424270681756574173171780701666419/647030592063612110784000000000000000000), (57552534261950699946222007924454230661/485272944047709083088000000000000000000), (4595383995724389339194122130458793951/40439412003975756924000000000000000000), (979514373321594851799916391336052923/10109853000993939231000000000000000000)]
    reserve := (18824200687/200000000000) }

theorem mixed_004_277_valid : mixed_004_277.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_277]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_277]
  · intro i; fin_cases i <;> norm_num [mixed_004_277]
  · norm_num [mixed_004_277]
  · norm_num [mixed_004_277, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_277, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_277, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_277, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_277]

def mixed_004_278 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(30524911/50000000), 0, (41103203/50000000), 0, 0], ![0, 0, (26115447/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (577517/100000000), (3264431/12500000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-34592169114444908552055013/2262317277392400000000000), (569395017/5775170), (-195606453201436508552055013/1131158638696200000000000), (569395017/5775170), (-356620737288428108552055013/2262317277392400000000000)]
    bernstein := [(2474205608706837093034390547/22623172773924000000000000000), (12404529942215295575615572937/90492691095696000000000000000), (159794698189905469363012017581/1085912293148352000000000000000), (201598277502082077551045399317/1447883057531136000000000000000), (653948506597215164632572463307/5791532230124544000000000000000)]
    reserve := (109365986523/1000000000000) }

theorem mixed_004_278_valid : mixed_004_278.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_278]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_278]
  · intro i; fin_cases i <;> norm_num [mixed_004_278]
  · norm_num [mixed_004_278]
  · norm_num [mixed_004_278, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_278, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_278, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_278, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_278]

def mixed_004_279 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(2582999/4000000), 0, (19887081/25000000), 0, 0], ![0, 0, (26115447/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (71153/12500000), (3264431/12500000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-24840276814657694648173271/1393644353658000000000000), (151493897/1423060), (-122220282388524194648173271/696822176829000000000000), (151493897/1423060), (-219600287962390694648173271/1393644353658000000000000)]
    bernstein := [(515774459835714753097844490169/3567729545364480000000000000000), (102854462752865499212300629497/594621590894080000000000000000), (491067540804500739181397027347/2675797159023360000000000000000), (26137213078319186082149792337/148655397723520000000000000000), (33321573439233174233620393129/222983096585280000000000000000)]
    reserve := (144566580307/1000000000000) }

theorem mixed_004_279_valid : mixed_004_279.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_279]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_279]
  · intro i; fin_cases i <;> norm_num [mixed_004_279]
  · norm_num [mixed_004_279]
  · norm_num [mixed_004_279, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_279, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_279, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_279, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_279]

def mixed_004_280 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 1, 0, 2, 0, 2, 1]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(13583621/20000000), 0, (19192791/25000000), 0, 0], ![0, 0, (26115447/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (560543/100000000), (3264431/12500000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-225687117940091736631685173/10979123676198000000000000), (320397734/2802715), (-977529620943143736631685173/5489561838099000000000000), (320397734/2802715), (-1729372123946195736631685173/10979123676198000000000000)]
    bernstein := [(314235498496942627315637438027/1756659788191680000000000000000), (146182140136763496479577675463/702663915276672000000000000000), (184737751281415488041979179273/843196698332006400000000000000), (23792104293952627085543809151/112426226444267520000000000000), (8326718578362657089749713083/44970490577707008000000000000)]
    reserve := (44720597097/250000000000) }

theorem mixed_004_280_valid : mixed_004_280.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_004_280]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_004_280]
  · intro i; fin_cases i <;> norm_num [mixed_004_280]
  · norm_num [mixed_004_280]
  · norm_num [mixed_004_280, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_004_280, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_004_280, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_004_280, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_004_280]

def mixedTable004 : OwnerTable where
  mode := .mixed
  owners := ![0, 1, 0, 2, 0, 2, 1]
  rows := [mixed_004_000, mixed_004_001, mixed_004_002, mixed_004_003, mixed_004_004, mixed_004_005, mixed_004_006, mixed_004_007, mixed_004_008, mixed_004_009, mixed_004_010, mixed_004_011, mixed_004_012, mixed_004_013, mixed_004_014, mixed_004_015, mixed_004_016, mixed_004_017, mixed_004_018, mixed_004_019, mixed_004_020, mixed_004_021, mixed_004_022, mixed_004_023, mixed_004_024, mixed_004_025, mixed_004_026, mixed_004_027, mixed_004_028, mixed_004_029, mixed_004_030, mixed_004_031, mixed_004_032, mixed_004_033, mixed_004_034, mixed_004_035, mixed_004_036, mixed_004_037, mixed_004_038, mixed_004_039, mixed_004_040, mixed_004_041, mixed_004_042, mixed_004_043, mixed_004_044, mixed_004_045, mixed_004_046, mixed_004_047, mixed_004_048, mixed_004_049, mixed_004_050, mixed_004_051, mixed_004_052, mixed_004_053, mixed_004_054, mixed_004_055, mixed_004_056, mixed_004_057, mixed_004_058, mixed_004_059, mixed_004_060, mixed_004_061, mixed_004_062, mixed_004_063, mixed_004_064, mixed_004_065, mixed_004_066, mixed_004_067, mixed_004_068, mixed_004_069, mixed_004_070, mixed_004_071, mixed_004_072, mixed_004_073, mixed_004_074, mixed_004_075, mixed_004_076, mixed_004_077, mixed_004_078, mixed_004_079, mixed_004_080, mixed_004_081, mixed_004_082, mixed_004_083, mixed_004_084, mixed_004_085, mixed_004_086, mixed_004_087, mixed_004_088, mixed_004_089, mixed_004_090, mixed_004_091, mixed_004_092, mixed_004_093, mixed_004_094, mixed_004_095, mixed_004_096, mixed_004_097, mixed_004_098, mixed_004_099, mixed_004_100, mixed_004_101, mixed_004_102, mixed_004_103, mixed_004_104, mixed_004_105, mixed_004_106, mixed_004_107, mixed_004_108, mixed_004_109, mixed_004_110, mixed_004_111, mixed_004_112, mixed_004_113, mixed_004_114, mixed_004_115, mixed_004_116, mixed_004_117, mixed_004_118, mixed_004_119, mixed_004_120, mixed_004_121, mixed_004_122, mixed_004_123, mixed_004_124, mixed_004_125, mixed_004_126, mixed_004_127, mixed_004_128, mixed_004_129, mixed_004_130, mixed_004_131, mixed_004_132, mixed_004_133, mixed_004_134, mixed_004_135, mixed_004_136, mixed_004_137, mixed_004_138, mixed_004_139, mixed_004_140, mixed_004_141, mixed_004_142, mixed_004_143, mixed_004_144, mixed_004_145, mixed_004_146, mixed_004_147, mixed_004_148, mixed_004_149, mixed_004_150, mixed_004_151, mixed_004_152, mixed_004_153, mixed_004_154, mixed_004_155, mixed_004_156, mixed_004_157, mixed_004_158, mixed_004_159, mixed_004_160, mixed_004_161, mixed_004_162, mixed_004_163, mixed_004_164, mixed_004_165, mixed_004_166, mixed_004_167, mixed_004_168, mixed_004_169, mixed_004_170, mixed_004_171, mixed_004_172, mixed_004_173, mixed_004_174, mixed_004_175, mixed_004_176, mixed_004_177, mixed_004_178, mixed_004_179, mixed_004_180, mixed_004_181, mixed_004_182, mixed_004_183, mixed_004_184, mixed_004_185, mixed_004_186, mixed_004_187, mixed_004_188, mixed_004_189, mixed_004_190, mixed_004_191, mixed_004_192, mixed_004_193, mixed_004_194, mixed_004_195, mixed_004_196, mixed_004_197, mixed_004_198, mixed_004_199, mixed_004_200, mixed_004_201, mixed_004_202, mixed_004_203, mixed_004_204, mixed_004_205, mixed_004_206, mixed_004_207, mixed_004_208, mixed_004_209, mixed_004_210, mixed_004_211, mixed_004_212, mixed_004_213, mixed_004_214, mixed_004_215, mixed_004_216, mixed_004_217, mixed_004_218, mixed_004_219, mixed_004_220, mixed_004_221, mixed_004_222, mixed_004_223, mixed_004_224, mixed_004_225, mixed_004_226, mixed_004_227, mixed_004_228, mixed_004_229, mixed_004_230, mixed_004_231, mixed_004_232, mixed_004_233, mixed_004_234, mixed_004_235, mixed_004_236, mixed_004_237, mixed_004_238, mixed_004_239, mixed_004_240, mixed_004_241, mixed_004_242, mixed_004_243, mixed_004_244, mixed_004_245, mixed_004_246, mixed_004_247, mixed_004_248, mixed_004_249, mixed_004_250, mixed_004_251, mixed_004_252, mixed_004_253, mixed_004_254, mixed_004_255, mixed_004_256, mixed_004_257, mixed_004_258, mixed_004_259, mixed_004_260, mixed_004_261, mixed_004_262, mixed_004_263, mixed_004_264, mixed_004_265, mixed_004_266, mixed_004_267, mixed_004_268, mixed_004_269, mixed_004_270, mixed_004_271, mixed_004_272, mixed_004_273, mixed_004_274, mixed_004_275, mixed_004_276, mixed_004_277, mixed_004_278, mixed_004_279, mixed_004_280]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact mixed_004_000_valid
    · exact mixed_004_001_valid
    · exact mixed_004_002_valid
    · exact mixed_004_003_valid
    · exact mixed_004_004_valid
    · exact mixed_004_005_valid
    · exact mixed_004_006_valid
    · exact mixed_004_007_valid
    · exact mixed_004_008_valid
    · exact mixed_004_009_valid
    · exact mixed_004_010_valid
    · exact mixed_004_011_valid
    · exact mixed_004_012_valid
    · exact mixed_004_013_valid
    · exact mixed_004_014_valid
    · exact mixed_004_015_valid
    · exact mixed_004_016_valid
    · exact mixed_004_017_valid
    · exact mixed_004_018_valid
    · exact mixed_004_019_valid
    · exact mixed_004_020_valid
    · exact mixed_004_021_valid
    · exact mixed_004_022_valid
    · exact mixed_004_023_valid
    · exact mixed_004_024_valid
    · exact mixed_004_025_valid
    · exact mixed_004_026_valid
    · exact mixed_004_027_valid
    · exact mixed_004_028_valid
    · exact mixed_004_029_valid
    · exact mixed_004_030_valid
    · exact mixed_004_031_valid
    · exact mixed_004_032_valid
    · exact mixed_004_033_valid
    · exact mixed_004_034_valid
    · exact mixed_004_035_valid
    · exact mixed_004_036_valid
    · exact mixed_004_037_valid
    · exact mixed_004_038_valid
    · exact mixed_004_039_valid
    · exact mixed_004_040_valid
    · exact mixed_004_041_valid
    · exact mixed_004_042_valid
    · exact mixed_004_043_valid
    · exact mixed_004_044_valid
    · exact mixed_004_045_valid
    · exact mixed_004_046_valid
    · exact mixed_004_047_valid
    · exact mixed_004_048_valid
    · exact mixed_004_049_valid
    · exact mixed_004_050_valid
    · exact mixed_004_051_valid
    · exact mixed_004_052_valid
    · exact mixed_004_053_valid
    · exact mixed_004_054_valid
    · exact mixed_004_055_valid
    · exact mixed_004_056_valid
    · exact mixed_004_057_valid
    · exact mixed_004_058_valid
    · exact mixed_004_059_valid
    · exact mixed_004_060_valid
    · exact mixed_004_061_valid
    · exact mixed_004_062_valid
    · exact mixed_004_063_valid
    · exact mixed_004_064_valid
    · exact mixed_004_065_valid
    · exact mixed_004_066_valid
    · exact mixed_004_067_valid
    · exact mixed_004_068_valid
    · exact mixed_004_069_valid
    · exact mixed_004_070_valid
    · exact mixed_004_071_valid
    · exact mixed_004_072_valid
    · exact mixed_004_073_valid
    · exact mixed_004_074_valid
    · exact mixed_004_075_valid
    · exact mixed_004_076_valid
    · exact mixed_004_077_valid
    · exact mixed_004_078_valid
    · exact mixed_004_079_valid
    · exact mixed_004_080_valid
    · exact mixed_004_081_valid
    · exact mixed_004_082_valid
    · exact mixed_004_083_valid
    · exact mixed_004_084_valid
    · exact mixed_004_085_valid
    · exact mixed_004_086_valid
    · exact mixed_004_087_valid
    · exact mixed_004_088_valid
    · exact mixed_004_089_valid
    · exact mixed_004_090_valid
    · exact mixed_004_091_valid
    · exact mixed_004_092_valid
    · exact mixed_004_093_valid
    · exact mixed_004_094_valid
    · exact mixed_004_095_valid
    · exact mixed_004_096_valid
    · exact mixed_004_097_valid
    · exact mixed_004_098_valid
    · exact mixed_004_099_valid
    · exact mixed_004_100_valid
    · exact mixed_004_101_valid
    · exact mixed_004_102_valid
    · exact mixed_004_103_valid
    · exact mixed_004_104_valid
    · exact mixed_004_105_valid
    · exact mixed_004_106_valid
    · exact mixed_004_107_valid
    · exact mixed_004_108_valid
    · exact mixed_004_109_valid
    · exact mixed_004_110_valid
    · exact mixed_004_111_valid
    · exact mixed_004_112_valid
    · exact mixed_004_113_valid
    · exact mixed_004_114_valid
    · exact mixed_004_115_valid
    · exact mixed_004_116_valid
    · exact mixed_004_117_valid
    · exact mixed_004_118_valid
    · exact mixed_004_119_valid
    · exact mixed_004_120_valid
    · exact mixed_004_121_valid
    · exact mixed_004_122_valid
    · exact mixed_004_123_valid
    · exact mixed_004_124_valid
    · exact mixed_004_125_valid
    · exact mixed_004_126_valid
    · exact mixed_004_127_valid
    · exact mixed_004_128_valid
    · exact mixed_004_129_valid
    · exact mixed_004_130_valid
    · exact mixed_004_131_valid
    · exact mixed_004_132_valid
    · exact mixed_004_133_valid
    · exact mixed_004_134_valid
    · exact mixed_004_135_valid
    · exact mixed_004_136_valid
    · exact mixed_004_137_valid
    · exact mixed_004_138_valid
    · exact mixed_004_139_valid
    · exact mixed_004_140_valid
    · exact mixed_004_141_valid
    · exact mixed_004_142_valid
    · exact mixed_004_143_valid
    · exact mixed_004_144_valid
    · exact mixed_004_145_valid
    · exact mixed_004_146_valid
    · exact mixed_004_147_valid
    · exact mixed_004_148_valid
    · exact mixed_004_149_valid
    · exact mixed_004_150_valid
    · exact mixed_004_151_valid
    · exact mixed_004_152_valid
    · exact mixed_004_153_valid
    · exact mixed_004_154_valid
    · exact mixed_004_155_valid
    · exact mixed_004_156_valid
    · exact mixed_004_157_valid
    · exact mixed_004_158_valid
    · exact mixed_004_159_valid
    · exact mixed_004_160_valid
    · exact mixed_004_161_valid
    · exact mixed_004_162_valid
    · exact mixed_004_163_valid
    · exact mixed_004_164_valid
    · exact mixed_004_165_valid
    · exact mixed_004_166_valid
    · exact mixed_004_167_valid
    · exact mixed_004_168_valid
    · exact mixed_004_169_valid
    · exact mixed_004_170_valid
    · exact mixed_004_171_valid
    · exact mixed_004_172_valid
    · exact mixed_004_173_valid
    · exact mixed_004_174_valid
    · exact mixed_004_175_valid
    · exact mixed_004_176_valid
    · exact mixed_004_177_valid
    · exact mixed_004_178_valid
    · exact mixed_004_179_valid
    · exact mixed_004_180_valid
    · exact mixed_004_181_valid
    · exact mixed_004_182_valid
    · exact mixed_004_183_valid
    · exact mixed_004_184_valid
    · exact mixed_004_185_valid
    · exact mixed_004_186_valid
    · exact mixed_004_187_valid
    · exact mixed_004_188_valid
    · exact mixed_004_189_valid
    · exact mixed_004_190_valid
    · exact mixed_004_191_valid
    · exact mixed_004_192_valid
    · exact mixed_004_193_valid
    · exact mixed_004_194_valid
    · exact mixed_004_195_valid
    · exact mixed_004_196_valid
    · exact mixed_004_197_valid
    · exact mixed_004_198_valid
    · exact mixed_004_199_valid
    · exact mixed_004_200_valid
    · exact mixed_004_201_valid
    · exact mixed_004_202_valid
    · exact mixed_004_203_valid
    · exact mixed_004_204_valid
    · exact mixed_004_205_valid
    · exact mixed_004_206_valid
    · exact mixed_004_207_valid
    · exact mixed_004_208_valid
    · exact mixed_004_209_valid
    · exact mixed_004_210_valid
    · exact mixed_004_211_valid
    · exact mixed_004_212_valid
    · exact mixed_004_213_valid
    · exact mixed_004_214_valid
    · exact mixed_004_215_valid
    · exact mixed_004_216_valid
    · exact mixed_004_217_valid
    · exact mixed_004_218_valid
    · exact mixed_004_219_valid
    · exact mixed_004_220_valid
    · exact mixed_004_221_valid
    · exact mixed_004_222_valid
    · exact mixed_004_223_valid
    · exact mixed_004_224_valid
    · exact mixed_004_225_valid
    · exact mixed_004_226_valid
    · exact mixed_004_227_valid
    · exact mixed_004_228_valid
    · exact mixed_004_229_valid
    · exact mixed_004_230_valid
    · exact mixed_004_231_valid
    · exact mixed_004_232_valid
    · exact mixed_004_233_valid
    · exact mixed_004_234_valid
    · exact mixed_004_235_valid
    · exact mixed_004_236_valid
    · exact mixed_004_237_valid
    · exact mixed_004_238_valid
    · exact mixed_004_239_valid
    · exact mixed_004_240_valid
    · exact mixed_004_241_valid
    · exact mixed_004_242_valid
    · exact mixed_004_243_valid
    · exact mixed_004_244_valid
    · exact mixed_004_245_valid
    · exact mixed_004_246_valid
    · exact mixed_004_247_valid
    · exact mixed_004_248_valid
    · exact mixed_004_249_valid
    · exact mixed_004_250_valid
    · exact mixed_004_251_valid
    · exact mixed_004_252_valid
    · exact mixed_004_253_valid
    · exact mixed_004_254_valid
    · exact mixed_004_255_valid
    · exact mixed_004_256_valid
    · exact mixed_004_257_valid
    · exact mixed_004_258_valid
    · exact mixed_004_259_valid
    · exact mixed_004_260_valid
    · exact mixed_004_261_valid
    · exact mixed_004_262_valid
    · exact mixed_004_263_valid
    · exact mixed_004_264_valid
    · exact mixed_004_265_valid
    · exact mixed_004_266_valid
    · exact mixed_004_267_valid
    · exact mixed_004_268_valid
    · exact mixed_004_269_valid
    · exact mixed_004_270_valid
    · exact mixed_004_271_valid
    · exact mixed_004_272_valid
    · exact mixed_004_273_valid
    · exact mixed_004_274_valid
    · exact mixed_004_275_valid
    · exact mixed_004_276_valid
    · exact mixed_004_277_valid
    · exact mixed_004_278_valid
    · exact mixed_004_279_valid
    · exact mixed_004_280_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
