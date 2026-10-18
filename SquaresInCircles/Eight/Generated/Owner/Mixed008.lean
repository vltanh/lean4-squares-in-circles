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

def mixed_008_000 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 2, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(64079547/100000000), 0, (19192791/25000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (560543/100000000)]
    alternative := .zero
    polynomial := [(-518679805801647026543526403/25500310721794000000000000), (-64079547/560543), (-2264922767067603026543526403/12750155360897000000000000), (-64079547/560543), (-4011165728333559026543526403/25500310721794000000000000)]
    bernstein := [(48676831744687163549547798413/104449272716468224000000000000), (127999766553700080280385637161/261123181791170560000000000000), (970227822043515549797898111503/1958423863433779200000000000000), (786924836166601277834152754593/1632019886194816000000000000000), (1839696557843460249798533628797/4080049715487040000000000000000)]
    reserve := (22545026239/50000000000) }

theorem mixed_008_000_valid : mixed_008_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_008_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_008_000]
  · intro i; fin_cases i <;> norm_num [mixed_008_000]
  · norm_num [mixed_008_000]
  · norm_num [mixed_008_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_008_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_008_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_008_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_008_000]

def mixed_008_001 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(60597559/100000000), 0, (19887081/25000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (71153/12500000)]
    alternative := .zero
    polynomial := [(-3562220206639771900012997/202306469885875000000000), (-60597559/569224), (-17698255066183490650012997/101153234942937500000000), (-60597559/569224), (-31834289925727209400012997/202306469885875000000000)]
    bernstein := [(13643920808794202435479791803/32369035181740000000000000000), (28858898127975434405825433177/64738070363480000000000000000), (175343518645345172133590587129/388428422180880000000000000000), (113646782124801563143789401537/258952281453920000000000000000), (211576280700232062890927695083/517904562907840000000000000000)]
    reserve := (51065460669/125000000000) }

theorem mixed_008_001_valid : mixed_008_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_008_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_008_001]
  · intro i; fin_cases i <;> norm_num [mixed_008_001]
  · norm_num [mixed_008_001]
  · norm_num [mixed_008_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_008_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_008_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_008_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_008_001]

def mixed_008_002 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 2, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(28469751/50000000), 0, (41103203/50000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (577517/100000000)]
    alternative := .zero
    polynomial := [(-198022822755422651814753033/13136247305843000000000000), (-56939502/577517), (-1132959525346459651814753033/6568123652921500000000000), (-56939502/577517), (-2067896227937496651814753033/13136247305843000000000000)]
    bernstein := [(12678838078989630820332633898087/33628793102958080000000000000000), (3374686266314741915529127349497/8407198275739520000000000000000), (2569063427926383781645466878321/6305398706804640000000000000000), (207836701201420769012252617917/525449892233720000000000000000), (48086875389600539788919214927/131362473058430000000000000000)]
    reserve := (45757812591/125000000000) }

theorem mixed_008_002_valid : mixed_008_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_008_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_008_002]
  · intro i; fin_cases i <;> norm_num [mixed_008_002]
  · norm_num [mixed_008_002]
  · norm_num [mixed_008_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_008_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_008_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_008_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_008_002]

def mixed_008_003 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(53110117/100000000), 0, (84730841/100000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (585377/100000000)]
    alternative := .zero
    polynomial := [(-339258122900483084710239531/26630062973566000000000000), (-53110117/585377), (-2266552526022922084710239531/13315031486783000000000000), (-53110117/585377), (-4193846929145361084710239531/26630062973566000000000000)]
    bernstein := [(88549459950464372557644132189/266300629735660000000000000000), (380287672412569559930824855393/1065202518942640000000000000000), (4645365163118474467814677763923/12782430227311680000000000000000), (6001359119702808706522473175517/17043240303082240000000000000000), (595968898346582133533498304417/1842512465198080000000000000000)]
    reserve := (80863618239/250000000000) }

theorem mixed_008_003_valid : mixed_008_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_008_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_008_003]
  · intro i; fin_cases i <;> norm_num [mixed_008_003]
  · norm_num [mixed_008_003]
  · norm_num [mixed_008_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_008_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_008_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_008_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_008_003]

def mixed_008_004 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 2, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(24557813/50000000), 0, (21776787/25000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (592757/100000000)]
    alternative := .zero
    polynomial := [(-142966363296431767024359563/13482897549803000000000000), (-49115626/592757), (-1133639398232777767024359563/6741448774901500000000000), (-49115626/592757), (-2124312433169123767024359563/13482897549803000000000000)]
    bernstein := [(9938248941318970912803847564517/34516217727495680000000000000000), (1078736354253315132634199845167/3451621772749568000000000000000), (330618300008552585049716301943/1035486531824870400000000000000), (10650183872248331260186750359/34516217727495680000000000000), (968615640366327329960086293/3451621772749568000000000000)]
    reserve := (280626240109/1000000000000) }

theorem mixed_008_004_valid : mixed_008_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_008_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_008_004]
  · intro i; fin_cases i <;> norm_num [mixed_008_004]
  · norm_num [mixed_008_004]
  · norm_num [mixed_008_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_008_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_008_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_008_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_008_004]

def mixed_008_005 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(44963763/100000000), 0, (44660553/50000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (299807/50000000)]
    alternative := .zero
    polynomial := [(-118196758484062380454882503/13638867413506000000000000), (-44963763/599614), (-1134049225205749380454882503/6819433706753000000000000), (-44963763/599614), (-2149901691927436380454882503/13638867413506000000000000)]
    bernstein := [(849105692367450048538956633/3491550057857536000000000000), (9353509417523663953122568881/34915500578575360000000000000), (96006953498040728465674791801/349155005785753600000000000000), (924388624438164875952884605233/3491550057857536000000000000000), (8292203723430385849430763440217/34915500578575360000000000000000)]
    reserve := (59373369893/250000000000) }

theorem mixed_008_005_valid : mixed_008_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_008_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_008_005]
  · intro i; fin_cases i <;> norm_num [mixed_008_005]
  · norm_num [mixed_008_005]
  · norm_num [mixed_008_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_008_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_008_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_008_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_008_005]

def mixed_008_006 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 2, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1270743/3125000), 0, (22839737/25000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (37869/6250000)]
    alternative := .zero
    polynomial := [(-1491821400650989586193607/215342816412750000000000), (-847162/12623), (-17726648342564208336193607/107671408206375000000000), (-847162/12623), (-11320491761492475695397869/71780938804250000000000)]
    bernstein := [(8405256148349670730035914621/42405970001280000000000000000), (15366968137530188609686246297/68909701252080000000000000000), (114482691873073718952429187/496944960952500000000000000), (39590046990767363728989927/179452347010625000000000000), (502020682995166629483109/2588255004960937500000000)]
    reserve := (193961059491/1000000000000) }

theorem mixed_008_006_valid : mixed_008_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_008_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_008_006]
  · intro i; fin_cases i <;> norm_num [mixed_008_006]
  · norm_num [mixed_008_006]
  · norm_num [mixed_008_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_008_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_008_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_008_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_008_006]

def mixed_008_007 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7245283/20000000), 0, (93207547/100000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (611587/100000000)]
    alternative := .zero
    polynomial := [(-149908395024032739852459171/27822412434746000000000000), (-36226415/611587), (-2270014622482245739852459171/13911206217373000000000000), (-36226415/611587), (-4390120849940458739852459171/27822412434746000000000000)]
    bernstein := [(664678619972722964934400101/4347251942929062500000000000), (12364789713874393557032370839/69556031086865000000000000000), (154746509435791199922404866547/834672373042380000000000000000), (1567400964127936400042029193347/8903171979118720000000000000000), (10678312058515352934453169757629/71225375832949760000000000000000)]
    reserve := (149922860127/1000000000000) }

theorem mixed_008_007_valid : mixed_008_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_008_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_008_007]
  · intro i; fin_cases i <;> norm_num [mixed_008_007]
  · norm_num [mixed_008_007]
  · norm_num [mixed_008_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_008_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_008_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_008_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_008_007]

def mixed_008_008 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 2, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7915969/25000000), 0, (4742731/5000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (616623/100000000)]
    alternative := .zero
    polynomial := [(-28383922986601322088284407/7012877735608500000000000), (-31663876/616623), (-189258864331782107362761469/1168812955934750000000000), (-31663876/616623), (-1107169263004091322088284407/7012877735608500000000000)]
    bernstein := [(1923546670314704326214952201193/17952967003157760000000000000000), (1185601518101417258540009555597/8976483501578880000000000000000), (628052489254716785345585433713/4488241750789440000000000000000), (293839559059889977297067257877/2244120875394720000000000000000), (118110278314806629749696112633/1122060437697360000000000000000)]
    reserve := (52630978843/500000000000) }

theorem mixed_008_008_valid : mixed_008_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_008_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_008_008]
  · intro i; fin_cases i <;> norm_num [mixed_008_008]
  · norm_num [mixed_008_008]
  · norm_num [mixed_008_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_008_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_008_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_008_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_008_008]

def mixed_008_009 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 2, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (767163/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(13494863/50000000), 0, (96288913/100000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (31049/5000000)]
    alternative := .zero
    polynomial := [(-256520803505416931307083/88280375858875000000000), (-13494863/310490), (-7100880872012063806307083/44140187929437500000000), (-13494863/310490), (-13945240940518710681307083/88280375858875000000000)]
    bernstein := [(859278346389710770269848677/14124860137420000000000000000), (484853562743085921800697639/5649944054968000000000000000), (636332975043539779155421991/6779932865961600000000000000), (15395700448460503810291123/180798209758976000000000000), (865669023315994859102973/14463856780718080000000000)]
    reserve := (29925248723/500000000000) }

theorem mixed_008_009_valid : mixed_008_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_008_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_008_009]
  · intro i; fin_cases i <;> norm_num [mixed_008_009]
  · norm_num [mixed_008_009]
  · norm_num [mixed_008_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_008_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_008_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_008_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_008_009]

def mixed_008_010 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 2, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098431/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(22218793/100000000), 0, (48750193/50000000), 0, 0]] i.1) i.2
    mu := ![(22746079/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (4997/800000)]
    alternative := .zero
    polynomial := [(-446272028351560338157829/227324313526000000000000), (-22218793/624625), (-957278099381237491481991/5982218777000000000000), (-22218793/624625), (-35930295748135464338157829/227324313526000000000000)]
    bernstein := [(515497600237074051326899/37244815528099840000000000), (9043030114791967119806063/232780097050624000000000000), (68426124440506322228940159/1454875606566400000000000000), (70131445258671153530800951/1818594508208000000000000000), (30801844227934206451986371/2273243135260000000000000000)]
    reserve := (13549735947/1000000000000) }

theorem mixed_008_010_valid : mixed_008_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_008_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_008_010]
  · intro i; fin_cases i <;> norm_num [mixed_008_010]
  · norm_num [mixed_008_010]
  · norm_num [mixed_008_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_008_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_008_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_008_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_008_010]

def mixed_008_011 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 1]
    lambda := ![(4086431/100000000), (2557973/20000000), (2557973/20000000), (4232349/25000000), (4232349/25000000), (4524473/25000000), (9188577/50000000)]
    cone := fun i => (![![0, 0, (118793/2000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(3191567/100000000), 0, 0, 0, 0]] i.1) i.2
    mu := ![(2322417/50000000), (1791083/50000000), (1/100000000), (1072251/20000000), (1/100000000), (1565467/25000000), (115323/100000000)]
    alternative := .zero
    polynomial := [(-894473377486188700297258009003926409003369/4473420433771190698045026864450000000000000), (-71546901842129853561/13770204320600000000), (-65972606622958801626442223541542831207503369/2236710216885595349022513432225000000000000), (-71546901842129853561/13770204320600000000), (-10080826143725493427122091467237056615846413/344109264136245438311155912650000000000000)]
    bernstein := [(1205015141699951079064136139315095349317132831/44734204337711906980450268644500000000000000000), (5563327263406519181439967820652330996756746593/178936817350847627921801074578000000000000000000), (69037358019163901922810556831611329035332445337/2147241808210171535061612894936000000000000000000), (86303636011656942828509097416297530687781574437/2862989077613562046748817193248000000000000000000), (22096890153098402039989851021727400452492466147/880919716188788322076559136384000000000000000000)]
    reserve := (25083886473/1000000000000) }

theorem mixed_008_011_valid : mixed_008_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_008_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_008_011]
  · intro i; fin_cases i <;> norm_num [mixed_008_011]
  · norm_num [mixed_008_011]
  · norm_num [mixed_008_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_008_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_008_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_008_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_008_011]

def mixed_008_012 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 2, 0, 2, 0, 2, 1]
    lambda := ![(4951353/100000000), (13048393/100000000), (13048393/100000000), (8493651/50000000), (8493651/50000000), (8710157/50000000), (1097309/6250000)]
    cone := fun i => (![![0, 0, (4884349/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(2186079/100000000), 0, 0, 0, 0]] i.1) i.2
    mu := ![(1139159/25000000), (462103/12500000), (1/100000000), (8457/156250), (1/100000000), (1537039/25000000), (55277/50000000)]
    alternative := .zero
    polynomial := [(-571606126037781822264689872047157517171/6175366298565994169232866400000000000000), (-72705223178558890307/20434934024800000000), (-86798100811575736070209216030257037517171/3087683149282997084616433200000000000000), (-72705223178558890307/20434934024800000000), (-173024595497113690318153742188466917517171/6175366298565994169232866400000000000000)]
    bernstein := [(265100191359503481355226239601517014308824349/15808937724328945073236137984000000000000000000), (164465115264950795429159742527799321697104383/7904468862164472536618068992000000000000000000), (259671752931367662707898855450634827954585583/11856703293246708804927103488000000000000000000), (39661984076876234827725249217971291523386487/1976117215541118134154517248000000000000000000), (15141073323356498825734417390543237341386029/988058607770559067077258624000000000000000000)]
    reserve := (15324063981/1000000000000) }

theorem mixed_008_012_valid : mixed_008_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_008_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_008_012]
  · intro i; fin_cases i <;> norm_num [mixed_008_012]
  · norm_num [mixed_008_012]
  · norm_num [mixed_008_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_008_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_008_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_008_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_008_012]

def mixed_008_013 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 1]
    lambda := ![(6725803/100000000), (15930943/100000000), (15930943/100000000), (20677083/100000000), (20677083/100000000), (1251871/12500000), (401727/4000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (2665529/50000000), 0], ![(37609/5000000), 0, 0, 0, 0]] i.1) i.2
    mu := ![(3054209/100000000), (904591/20000000), (1/100000000), (6595561/100000000), (1/100000000), (2741901/50000000), (63379/100000000)]
    alternative := .zero
    polynomial := [(-8389665816566986355522745835982959128169/741603949331412440729138544300000000000000), (-36510229987878116979/28666036494500000000), (-6011138293773914519001215599275914608128169/370801974665706220364569272150000000000000), (-36510229987878116979/28666036494500000000), (-12013886921731262051646908452715846257128169/741603949331412440729138544300000000000000)]
    bernstein := [(1411915306245725657904787304953744829825296631/118656631893025990516662167088000000000000000000), (1112352619229562333833756794520294413413329677/79104421262017327011108111392000000000000000000), (20689549747614980917252897581807862502391656693/1423879582716311886199946005056000000000000000000), (4212339618363628981268469325012004926729982077/316417685048069308044432445568000000000000000000), (19762945518991890471932491632060848786604091031/1898506110288415848266594673408000000000000000000)]
    reserve := (10409735007/1000000000000) }

theorem mixed_008_013_valid : mixed_008_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_008_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_008_013]
  · intro i; fin_cases i <;> norm_num [mixed_008_013]
  · norm_num [mixed_008_013]
  · norm_num [mixed_008_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_008_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_008_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_008_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_008_013]

def mixed_008_014 : Row :=
  { mode := .mixed
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 2, 0, 2, 0, 2, 1]
    lambda := ![(870183/12500000), (15834627/100000000), (15834627/100000000), (21018989/100000000), (21018989/100000000), (9664143/100000000), (9667163/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (5677423/100000000), 0], ![(241641/100000000), 0, 0, 0, 0]] i.1) i.2
    mu := ![(150507/5000000), (556303/12500000), (1/100000000), (3324767/50000000), (1/100000000), (5482209/100000000), (61063/100000000)]
    alternative := .zero
    polynomial := [(12551518917768628722952205290831542433553/3106288488470674988329598742300000000000000), (-47934859242387321/106154781528125000), (-24242031802941625880048584367867215573066447/1553144244235337494164799371150000000000000), (-47934859242387321/106154781528125000), (-48496615124801020388820120941025262688566447/3106288488470674988329598742300000000000000)]
    bernstein := [(44335499231101345634461899151574798841554483153/7952098530484927970123772780288000000000000000000), (37929088220203408778768680270995766730018353/4970061581553079981327357987680000000000000000), (120165105210484887499411704686926966347987953/14910184744659239943982073963040000000000000000), (21318169564449576171836549421956831833553/3106288488470674988329598742300000000000000), (12551518917768628722952205290831542433553/3106288488470674988329598742300000000000000)]
    reserve := (4040680369/1000000000000) }

theorem mixed_008_014_valid : mixed_008_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_008_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_008_014]
  · intro i; fin_cases i <;> norm_num [mixed_008_014]
  · norm_num [mixed_008_014]
  · norm_num [mixed_008_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_008_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_008_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_008_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_008_014]

def mixed_008_015 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 1]
    lambda := ![(7180809/100000000), (3973203/25000000), (3973203/25000000), (21257467/100000000), (21257467/100000000), (929411/10000000), (2306131/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (2990839/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2953827/100000000), (4406681/100000000), (1/100000000), (1341311/20000000), (1/100000000), (341169/6250000), (5913/5000000)]
    alternative := .zero
    polynomial := [(7319801716586705657677745487176780981/3623575643268593292489907575000000000000), (1575986425279/3553775000000), (-1522588981699409324530689064859733329891/201309757959366294027217087500000000000), (1575986425279/3553775000000), (-27413921472305954547210080912962376719019/3623575643268593292489907575000000000000)]
    bernstein := [(7319801716586705657677745487176780981/3623575643268593292489907575000000000000), (17363181687116148402157359271654824731/3623575643268593292489907575000000000000), (39282731707134717861027089695233389579927/5797721029229749267983852120000000000000000), (46226649149755899747754816975024337644331/5797721029229749267983852120000000000000000), (25923068110026518039886629326525034837926727/3092117882255866276258054464000000000000000000)]
    reserve := (3232079/1600000000) }

theorem mixed_008_015_valid : mixed_008_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_008_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_008_015]
  · intro i; fin_cases i <;> norm_num [mixed_008_015]
  · norm_num [mixed_008_015]
  · norm_num [mixed_008_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_008_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_008_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_008_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_008_015]

def mixed_008_016 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 2, 0, 2, 0, 2, 1]
    lambda := ![(462691/6250000), (16090191/100000000), (16090191/100000000), (10679389/50000000), (10679389/50000000), (223497/2500000), (4379563/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (6209449/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(181117/6250000), (2194811/50000000), (1/100000000), (3378483/50000000), (1/100000000), (2706757/50000000), (113971/50000000)]
    alternative := .zero
    polynomial := [(-3556447909776598436715581360143886657/1528918976678125418064543150000000000000), (4900377235111/10974055000000), (-2875730907853332775952848157796390386657/764459488339062709032271575000000000000), (4900377235111/10974055000000), (-442146566753606842574536979556356683589/117609152052163493697272550000000000000)]
    bernstein := [(25409220859705305213176131338017593483890943/3914032580296001070245230464000000000000000000), (19816736338621625012654109606626994462143/2443216342257179194909632000000000000000000), (27418339384430382199765331588984856397283629/2935524435222000802683922848000000000000000000), (6217918682130049724306944717239158450543/610804085564294798727408000000000000000000), (2600103392358040494641930520056825788667743/244627036268500066890326904000000000000000000)]
    reserve := (649182661/100000000000) }

theorem mixed_008_016_valid : mixed_008_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_008_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_008_016]
  · intro i; fin_cases i <;> norm_num [mixed_008_016]
  · norm_num [mixed_008_016]
  · norm_num [mixed_008_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_008_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_008_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_008_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_008_016]

def mixed_008_017 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 1]
    lambda := ![(7657181/100000000), (4063789/25000000), (4063789/25000000), (10708647/50000000), (10708647/50000000), (539303/6250000), (523067/6250000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (6394223/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1433131/50000000), (4362159/100000000), (1/100000000), (67939/1000000), (1/100000000), (5368397/100000000), (327827/100000000)]
    alternative := .zero
    polynomial := [(-258071679926197734160430208766899610290283/37373681545330121482783752924450000000000000), (49370779292033/109053975000000), (-47497574427441682017886176748833158500290283/18686840772665060741391876462225000000000000), (49370779292033/109053975000000), (-94737077174957166301611923288899417390290283/37373681545330121482783752924450000000000000)]
    bernstein := [(18770753729293629888035344647949028364550734439/1993263015750939812415133489304000000000000000000), (42541361613498049463614697608982543381362667717/3986526031501879624830266978608000000000000000000), (836966235821108935090272657312353610557522613959/71757468567033833246944805614944000000000000000000), (592931404814202145416208736526247945985246526359/47838312378022555497963203743296000000000000000000), (1230601150757289239322501449148636587116781856677/95676624756045110995926407486592000000000000000000)]
    reserve := (4708549143/500000000000) }

theorem mixed_008_017_valid : mixed_008_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_008_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_008_017]
  · intro i; fin_cases i <;> norm_num [mixed_008_017]
  · norm_num [mixed_008_017]
  · norm_num [mixed_008_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_008_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_008_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_008_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_008_017]

def mixed_008_018 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 2, 0, 2, 0, 2, 1]
    lambda := ![(794013/10000000), (128089/781250), (128089/781250), (10721833/50000000), (10721833/50000000), (521657/6250000), (4017621/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (6548577/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1427199/50000000), (2162661/50000000), (1/100000000), (3410337/50000000), (1/100000000), (5322663/100000000), (1677/400000)]
    alternative := .zero
    polynomial := [(-683591740003134680780714748305602766449/57998571393815509333082947650000000000000), (8320481744867/18022175000000), (-56582026886962917440182139501841520622449/28999285696907754666541473825000000000000), (8320481744867/18022175000000), (-112480462033922700199583564255377438478449/57998571393815509333082947650000000000000)]
    bernstein := [(137030392398318276675662435443903730855944187/11421257136012900299437872768000000000000000000), (485605706595820444729505119209802144180150277/37119085692041925973173086496000000000000000000), (388850203878901034753269277039466113711684177/27839314269031444479879814872000000000000000000), (33994690791210175449103627736804647335890353/2319942855752620373323317906000000000000000000), (8779757977804403902555400384300408232541751/579985713938155093330829476500000000000000000)]
    reserve := (5998918979/500000000000) }

theorem mixed_008_018_valid : mixed_008_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_008_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_008_018]
  · intro i; fin_cases i <;> norm_num [mixed_008_018]
  · norm_num [mixed_008_018]
  · norm_num [mixed_008_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_008_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_008_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_008_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_008_018]

def mixed_008_019 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 2, 0, 2, 0, 2, 1]
    lambda := ![(10262531/100000000), (9842931/50000000), (9842931/50000000), (25182873/100000000), (25182873/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (1026253/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (3147859/25000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(14669/800000), (5134083/100000000), (1/100000000), (1615343/20000000), (1/100000000), (1124867/25000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-252082818814424389621624713173510351/13684512296357842192178700000000000000), (1463962094469/3720350000000), (-2945997024848460229751698388567510351/6842256148178921096089350000000000000), (1463962094469/3720350000000), (-5639911230882496069881772063961510351/13684512296357842192178700000000000000)]
    bernstein := [(2323052873037535267983392760284012909449/136845122963578421921787000000000000000000), (691905088738924934506205869308918272823/36492032790287579179143200000000000000000), (5493941907157816366491810204977487719863/262742636090070570089831040000000000000000), (106616390915242130655282587263160066799/4670980197156810134930329600000000000000), (55394980293097130487618660073874350681/2242070494635268864766558208000000000000)]
    reserve := (16975781253/1000000000000) }

theorem mixed_008_019_valid : mixed_008_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_008_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_008_019]
  · intro i; fin_cases i <;> norm_num [mixed_008_019]
  · norm_num [mixed_008_019]
  · norm_num [mixed_008_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_008_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_008_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_008_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_008_019]

def mixed_008_020 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 2, 0, 2, 0, 2, 1]
    lambda := ![(5549277/50000000), (4944971/25000000), (4944971/25000000), (24670839/100000000), (24670839/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (5549277/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (12335419/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(991499/50000000), (1273383/25000000), (1/100000000), (399501/5000000), (1/100000000), (2203991/50000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-94242134278418119606405350093023279/4117325968858505314646100000000000000), (9147004611989/21223050000000), (-908644434820506594977238940617023279/2058662984429252657323050000000000000), (9147004611989/21223050000000), (-1723046735362595070348072531141023279/4117325968858505314646100000000000000)]
    bernstein := [(16748666856978194356589648427096665849/674582686737777510751617024000000000000), (227149573265079649040693321237350471799/8432283584222218884395212800000000000000), (9174773436516609884555416123891429128283/316210634408333208164820480000000000000000), (2728112447808854121743560106296734352969/87836287335648113379116800000000000000000), (21786719455206662332031789230311404865601/658772155017360850343376000000000000000000)]
    reserve := (12414094807/500000000000) }

theorem mixed_008_020_valid : mixed_008_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_008_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_008_020]
  · intro i; fin_cases i <;> norm_num [mixed_008_020]
  · norm_num [mixed_008_020]
  · norm_num [mixed_008_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_008_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_008_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_008_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_008_020]

def mixed_008_021 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 1]
    lambda := ![0, (22591853/100000000), (22591853/100000000), (27408147/100000000), (27408147/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (13395077/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (6852037/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (5557593/100000000), (1/100000000), (8974937/100000000), (1/100000000), (2448531/50000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-38164687153030748230659292799501/1017753274534657786425000000000000), (302619610507681/555759300000000), (-281948574294951860363527849105751/508876637267328893212500000000000), (302619610507681/555759300000000), (-525732461436872972496396405412001/1017753274534657786425000000000000)]
    bernstein := [(5420675479982718994523019326495060719/162840523925545245828000000000000000000), (11671997613526253335248355061320846211/325681047851090491656000000000000000000), (74938767824788549021795657939123501477/1954086287106542949936000000000000000000), (53180161842430772316071856285352348171/1302724191404361966624000000000000000000), (112703742361792952296816143111771468799/2605448382808723933248000000000000000000)]
    reserve := (33288246373/1000000000000) }

theorem mixed_008_021_valid : mixed_008_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_008_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_008_021]
  · intro i; fin_cases i <;> norm_num [mixed_008_021]
  · norm_num [mixed_008_021]
  · norm_num [mixed_008_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_008_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_008_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_008_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_008_021]

def mixed_008_022 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 2, 0, 2, 0, 2, 1]
    lambda := ![0, (22960111/100000000), (22960111/100000000), (27039889/100000000), (27039889/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (908341/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (2703989/20000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2770531/50000000), (1/100000000), (8963277/100000000), (1/100000000), (150977/3125000), (1/100000000)]
    alternative := .zero
    polynomial := [(-35098248486488435901245140923197/749843479091392999800000000000000), (20855610185851/34631637500000), (-218552274324140103125923430523197/374921739545696499900000000000000), (20855610185851/34631637500000), (-402006300161791770350601720123197/749843479091392999800000000000000)]
    bernstein := [(4906527495751363605324295155214270259/112917606263174475264000000000000000000), (217436613568473383391424349835442479/4704900260965603136000000000000000000), (1100909400637588252493102072400078829/22495304372741789994000000000000000000), (32260110869585944834785493869492291/624869565909494166500000000000000000), (6359363595501838590447818499179707/117163043608030156218750000000000000)]
    reserve := (8690456091/200000000000) }

theorem mixed_008_022_valid : mixed_008_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_008_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_008_022]
  · intro i; fin_cases i <;> norm_num [mixed_008_022]
  · norm_num [mixed_008_022]
  · norm_num [mixed_008_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_008_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_008_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_008_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_008_022]

def mixed_008_023 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 1]
    lambda := ![0, (11668431/50000000), (11668431/50000000), (13331569/50000000), (13331569/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (489511/3125000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (13331569/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2755409/50000000), (1/100000000), (4476667/50000000), (1/100000000), (95279/2000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-3404928589575144816186526169653/58763554500722401850000000000000), (5711825327241/8610653125000), (-18093009533186700394201838369653/29381777250361200925000000000000), (5711825327241/8610653125000), (-32781090476798255972217150569653/58763554500722401850000000000000)]
    bernstein := [(38498979740229527331096367594511/706292722364451945312500000000000), (649799426769441120045474503442523/11300683557831231125000000000000000), (106579388942273952140468239595430149/1762906635021672055500000000000000000), (29067182653641090088240785068643443/458642376591004112000000000000000000), (243122168434892760401774340308945587/3669139012728032896000000000000000000)]
    reserve := (54508532399/1000000000000) }

theorem mixed_008_023_valid : mixed_008_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_008_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_008_023]
  · intro i; fin_cases i <;> norm_num [mixed_008_023]
  · norm_num [mixed_008_023]
  · norm_num [mixed_008_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_008_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_008_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_008_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_008_023]

def mixed_008_024 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 2, 0, 2, 0, 2, 1]
    lambda := ![0, (11860329/50000000), (11860329/50000000), (13139671/50000000), (13139671/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (8391831/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (13139671/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (5466583/100000000), (1/100000000), (8945277/100000000), (1/100000000), (293461/6250000), (1/100000000)]
    alternative := .zero
    polynomial := [(-25499983567674633423086718461323/358756800125478683775000000000000), (99529876572399/136664575000000), (-117131329104490739977511685536323/179378400062739341887500000000000), (99529876572399/136664575000000), (-208762674641306846531936652611323/358756800125478683775000000000000)]
    bernstein := [(61103014275729332072944379441695308197/918417408321225430464000000000000000000), (6407943113162241652603855171850860253/91841740832122543046400000000000000000), (2010704929396713273113732163981430223/27552522249636762913920000000000000000), (69935947705232561139428455545469021/918417408321225430464000000000000000), (46380449955205912521866678268329/584979240968933395200000000000000)]
    reserve := (13306153329/200000000000) }

theorem mixed_008_024_valid : mixed_008_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_008_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_008_024]
  · intro i; fin_cases i <;> norm_num [mixed_008_024]
  · norm_num [mixed_008_024]
  · norm_num [mixed_008_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_008_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_008_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_008_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_008_024]

def mixed_008_025 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 1]
    lambda := ![0, (649727/2000000), (649727/2000000), (350273/1000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (12050819/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(350273/20000000), 0, (350273/1000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (7287097/100000000), (1/100000000), (6035661/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-3107439164744528898920657/21991223583058500000000000), (7829742476413/7287097000000), (-10842305918531070963583157/10995611791529250000000000), (7829742476413/7287097000000), (-18577172672317613028245657/21991223583058500000000000)]
    bernstein := [(445725436127687093775405127/5629753237262976000000000000), (523794241256098349693552789/6255281374736640000000000000), (149043824041188318819373900477/1688925971178892800000000000000), (57991586312342764985057761757/625528137473664000000000000000), (5467526010975728964346835025463/56297532372629760000000000000000)]
    reserve := (79173174621/1000000000000) }

theorem mixed_008_025_valid : mixed_008_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_008_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_008_025]
  · intro i; fin_cases i <;> norm_num [mixed_008_025]
  · norm_num [mixed_008_025]
  · norm_num [mixed_008_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_008_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_008_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_008_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_008_025]

def mixed_008_026 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 2, 0, 2, 0, 2, 1]
    lambda := ![0, (16363753/50000000), (16363753/50000000), (34544989/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (6334531/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1727249/100000000), 0, (34544989/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1425263/20000000), (1/100000000), (12024079/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-8553040755699536722639333/52461657880950000000000000), (2115442870507/1817937500000), (-27248608118084697112819333/26230828940475000000000000), (2115442870507/1817937500000), (-45944175480469857502999333/52461657880950000000000000)]
    bernstein := [(13108120197950196591267176547947/134301844175232000000000000000000), (3441436427729123619824500043731/33575461043808000000000000000000), (93211485315596664487517939041/868330889064000000000000000000), (235329958371249365900972480399/2098466315238000000000000000000), (61324326842603257352732924627/524616578809500000000000000000)]
    reserve := (48800968737/500000000000) }

theorem mixed_008_026_valid : mixed_008_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_008_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_008_026]
  · intro i; fin_cases i <;> norm_num [mixed_008_026]
  · norm_num [mixed_008_026]
  · norm_num [mixed_008_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_008_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_008_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_008_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_008_026]

def mixed_008_027 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 2, 0, 2, 0, 2, 1]
    lambda := ![0, (6593593/20000000), (6593593/20000000), (34064071/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (26521543/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(425801/25000000), 0, (34064071/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (868697/12500000), (1/100000000), (2994583/25000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1172474406728839142329360429/6243324644042400000000000000), (174872260273999/138991520000000), (-3427147551883646939770735429/3121662322021200000000000000), (174872260273999/138991520000000), (-5681820697038454737212110429/6243324644042400000000000000)]
    bernstein := [(7332151729366878512208740993051/62433246440424000000000000000000), (30641029476298173398572478861921/249732985761696000000000000000000), (383298777418544552612344599495173/2996795829140352000000000000000000), (531685997635422050213075337332461/3995727772187136000000000000000000), (2208482106167041572268557895794131/15982911088748544000000000000000000)]
    reserve := (117439860129/1000000000000) }

theorem mixed_008_027_valid : mixed_008_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_008_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_008_027]
  · intro i; fin_cases i <;> norm_num [mixed_008_027]
  · norm_num [mixed_008_027]
  · norm_num [mixed_008_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_008_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_008_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_008_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_008_027]

def mixed_008_028 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 2, 0, 2, 0, 2, 1]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (41631471/50000000), 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (20350399/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-3587082107763798869/4070079800000000000), (83262942/20350399), (-8073476617763798869/2035039900000000000), (83262942/20350399), (-12559871127763798869/4070079800000000000)]
    bernstein := [(1410594187349950607507291/10419404288000000000000000), (782970937210383262458449/5209702144000000000000000), (1289393071544137250690633/7814553216000000000000000), (233793012227942388266729/1302425536000000000000000), (126212035587690384210731/651212768000000000000000)]
    reserve := (1692268277/12500000000) }

theorem mixed_008_028_valid : mixed_008_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_008_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_008_028]
  · intro i; fin_cases i <;> norm_num [mixed_008_028]
  · norm_num [mixed_008_028]
  · norm_num [mixed_008_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_008_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_008_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_008_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_008_028]

def mixed_008_029 : Row :=
  { mode := .mixed
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 2, 0, 2, 0, 2, 1]
    lambda := ![0, (99999999/100000000), 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (85870743/100000000), 0, 0], ![0, 0, (99999999/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (19590439/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-15187964475643848549/15672351200000000000), (780643110375387/178094900000000), (-32577730361746187949/7836175600000000000), (780643110375387/178094900000000), (-49967496247848527349/15672351200000000000)]
    bernstein := [(491174576026770110554251/2507576192000000000000000), (212375567926557398626119/1003030476800000000000000), (91233188451450767119683/401212190720000000000000), (38974676086665298123263/160484876288000000000000), (16569617120191123222779/64193950515200000000000)]
    reserve := (195876232033/1000000000000) }

theorem mixed_008_029_valid : mixed_008_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [mixed_008_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [mixed_008_029]
  · intro i; fin_cases i <;> norm_num [mixed_008_029]
  · norm_num [mixed_008_029]
  · norm_num [mixed_008_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [mixed_008_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [mixed_008_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [mixed_008_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [mixed_008_029]

def mixedTable008 : OwnerTable where
  mode := .mixed
  owners := ![0, 2, 0, 2, 0, 2, 1]
  rows := [mixed_008_000, mixed_008_001, mixed_008_002, mixed_008_003, mixed_008_004, mixed_008_005, mixed_008_006, mixed_008_007, mixed_008_008, mixed_008_009, mixed_008_010, mixed_008_011, mixed_008_012, mixed_008_013, mixed_008_014, mixed_008_015, mixed_008_016, mixed_008_017, mixed_008_018, mixed_008_019, mixed_008_020, mixed_008_021, mixed_008_022, mixed_008_023, mixed_008_024, mixed_008_025, mixed_008_026, mixed_008_027, mixed_008_028, mixed_008_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact mixed_008_000_valid
    · exact mixed_008_001_valid
    · exact mixed_008_002_valid
    · exact mixed_008_003_valid
    · exact mixed_008_004_valid
    · exact mixed_008_005_valid
    · exact mixed_008_006_valid
    · exact mixed_008_007_valid
    · exact mixed_008_008_valid
    · exact mixed_008_009_valid
    · exact mixed_008_010_valid
    · exact mixed_008_011_valid
    · exact mixed_008_012_valid
    · exact mixed_008_013_valid
    · exact mixed_008_014_valid
    · exact mixed_008_015_valid
    · exact mixed_008_016_valid
    · exact mixed_008_017_valid
    · exact mixed_008_018_valid
    · exact mixed_008_019_valid
    · exact mixed_008_020_valid
    · exact mixed_008_021_valid
    · exact mixed_008_022_valid
    · exact mixed_008_023_valid
    · exact mixed_008_024_valid
    · exact mixed_008_025_valid
    · exact mixed_008_026_valid
    · exact mixed_008_027_valid
    · exact mixed_008_028_valid
    · exact mixed_008_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
