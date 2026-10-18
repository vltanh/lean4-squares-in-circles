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

def tilt_039_000 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/20), (1001/20000)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3688541/25000000), (3688541/25000000), (9349601/100000000), (7326259/50000000), (7326259/50000000), (8050217/50000000), (15736601/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5450711/100000000), (1/100000000), (420987/10000000), (4391957/100000000), (1/100000000), (5500817/100000000), (412481/100000000)]
    alternative := .zero
    polynomial := [(-745072104286892165406433904352913083832111931/46667548376311469441519940017700000000000000000), (16902727212019/26311687500000), (-150957989552840920604253291198719287200832111931/23333774188155734720759970008850000000000000000), (16902727212019/26311687500000), (-301170907001394949043100148493085661317832111931/46667548376311469441519940017700000000000000000)]
    bernstein := [(155760583871735102774420053484795857646569383269/7466807740209835110643190402832000000000000000000000), (51828242062636476253390752575825305836964902128223/2488935913403278370214396800944000000000000000000000000), (465566218185977773492463857972761883181494154159905807/22400423220629505331929571208496000000000000000000000000000), (51624207780903575919980050816381014318432791116355565023/2488935913403278370214396800944000000000000000000000000000000), (51512125959496268471366825442371039235573847228271111388023/2488935913403278370214396800944000000000000000000000000000000000)]
    reserve := (4139289/200000000000) }

theorem tilt_039_000_valid : tilt_039_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_039_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_039_000]
  · intro i; fin_cases i <;> norm_num [tilt_039_000]
  · norm_num [tilt_039_000]
  · norm_num [tilt_039_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_039_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_039_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_039_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_039_000]

def tilt_039_001 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/20), (1001/20000)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3688541/25000000), (3688541/25000000), (9349601/100000000), (7326259/50000000), (7326259/50000000), (8050217/50000000), (15736601/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(7377/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5450711/100000000), (1/100000000), (420987/10000000), (4391957/100000000), (1/100000000), (5500817/100000000), (208199/50000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-46508988880151100446988319698343585991373499/2944419532172291458956597392287500000000000000), (5577277526116210094021/8764907241300000000000), (-9439366253704283832913585544486795819201748499/1472209766086145729478298696143750000000000000), (5577277526116210094021/8764907241300000000000), (-18832223518528416565380182769275248052412123499/2944419532172291458956597392287500000000000000)]
    bernstein := [(14430481026622997122801118818930493943706737301/471107125147566633433055582766000000000000000000000), (4803728895453241766806785574665762863900361300967/157035708382522211144351860922000000000000000000000000), (43171901002825284479804319583676355077568652994885903/1413321375442699900299166748298000000000000000000000000000), (4789607320301611169902232132704447392737994300446718167/157035708382522211144351860922000000000000000000000000000000), (281289246211094841854508354619488996040136248590988232951/9237394610736600655550109466000000000000000000000000000000000)]
    reserve := (6090229/200000000000) }

theorem tilt_039_001_valid : tilt_039_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_039_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_039_001]
  · intro i; fin_cases i <;> norm_num [tilt_039_001]
  · norm_num [tilt_039_001]
  · norm_num [tilt_039_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_039_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_039_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_039_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_039_001]

def tilt_039_002 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/20), (1001/20000)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3688541/25000000), (3688541/25000000), (9349601/100000000), (7326259/50000000), (7326259/50000000), (8050217/50000000), (15736601/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (437/10000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5450711/100000000), (959/25000000), (420987/10000000), (4391957/100000000), (1/100000000), (5500817/100000000), (204283/50000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-25506523019161067911484399161154252941634337283/1583192910145256290511946554155350000000000000000), (5578035635272623758779/8600048732100000000000), (-5167811506468964096948321070329297813164230837283/791596455072628145255973277077675000000000000000), (5578035635272623758779/8600048732100000000000), (-10310116489918767125985157741497441373386827337283/1583192910145256290511946554155350000000000000000)]
    bernstein := [(9870548745294641888471074186269591746762467556317/253310865623241006481911448664856000000000000000000000), (3287417028284118705248744521090620895242324447188839/84436955207747002160637149554952000000000000000000000000), (29559793024288952226359254993094189210826127511526176951/759932596869723019445734345994568000000000000000000000000000), (3281196169950248136920911300824132449889422394140260371239/84436955207747002160637149554952000000000000000000000000000000), (3277741194976515216118788974464361605141580691735483908510239/84436955207747002160637149554952000000000000000000000000000000000)]
    reserve := (38818799/1000000000000) }

theorem tilt_039_002_valid : tilt_039_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_039_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_039_002]
  · intro i; fin_cases i <;> norm_num [tilt_039_002]
  · norm_num [tilt_039_002]
  · norm_num [tilt_039_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_039_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_039_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_039_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_039_002]

def tilt_039_003 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/20), (1001/20000)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3688541/25000000), (3688541/25000000), (9349601/100000000), (7326259/50000000), (7326259/50000000), (8050217/50000000), (15736601/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(680999/12500000), (1/100000000), (420987/10000000), (4391957/100000000), (1/100000000), (5500817/100000000), (208199/50000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-162153311803786611089115468194435006236252279/10300327644542950949926266186450000000000000000), (5577277526116210094021/8764907241300000000000), (-33020754570550241498709568436173091938550752279/5150163822271475474963133093225000000000000000), (5577277526116210094021/8764907241300000000000), (-65879355829296696386330021404151748870865252279/10300327644542950949926266186450000000000000000)]
    bernstein := [(138431330532072476416842211222119362884098284521/1648052423126872151988202589832000000000000000000000), (46121351117931466260367619077316355813439355285707/549350807708957383996067529944000000000000000000000000), (414877119215497013831272737341695237817587744578057563/4944157269380616455964607769496000000000000000000000000000), (6581728078718019620725713918732206821134924541086276701/78478686815565340570866789992000000000000000000000000000000), (2708545158124683526081459127439323023449568616740102973171/32314753394644551999768678232000000000000000000000000000000000)]
    reserve := (41908801/500000000000) }

theorem tilt_039_003_valid : tilt_039_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_039_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_039_003]
  · intro i; fin_cases i <;> norm_num [tilt_039_003]
  · norm_num [tilt_039_003]
  · norm_num [tilt_039_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_039_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_039_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_039_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_039_003]

def tilt_039_004 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/20), (1001/20000)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3688541/25000000), (3688541/25000000), (9349601/100000000), (7326259/50000000), (7326259/50000000), (8050217/50000000), (15736601/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(681679/12500000), (1/100000000), (420987/10000000), (4391957/100000000), (1/100000000), (5500817/100000000), (204283/50000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-162314989103859723001661001513890610219511609/10116681287069212601925047602650000000000000000), (5578035635272623758779/8600048732100000000000), (-33021899102385618936683955711050930272043011609/5058340643534606300962523801325000000000000000), (5578035635272623758779/8600048732100000000000), (-65881483215667378150366250420587969933866511609/10116681287069212601925047602650000000000000000)]
    bernstein := [(171285801914730974499512138293862576850336761191/1618669005931074016308007616424000000000000000000000), (57077683103074291050153733595798230120249014178597/539556335310358005436002538808000000000000000000000000), (513527680558991957258446287092430015428921181542567573/4856007017793222048924022849272000000000000000000000000000), (8148301643475308831655147570352256428131147134783121971/77079476472908286490857505544000000000000000000000000000000), (57016124085345554653752273067431775815801605739625744350797/539556335310358005436002538808000000000000000000000000000000000)]
    reserve := (21134447/200000000000) }

theorem tilt_039_004_valid : tilt_039_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_039_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_039_004]
  · intro i; fin_cases i <;> norm_num [tilt_039_004]
  · norm_num [tilt_039_004]
  · norm_num [tilt_039_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_039_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_039_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_039_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_039_004]

def tilt_039_005 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/20), (1001/20000)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3688541/25000000), (3688541/25000000), (9349601/100000000), (7326259/50000000), (7326259/50000000), (8050217/50000000), (15736601/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5450711/100000000), (1/100000000), (420987/10000000), (877993/20000000), (1/100000000), (5500817/100000000), (208199/50000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-37199469378105611661690963419891314830114263/2354467257589768474439690383350000000000000000), (5577277526116210094021/8764907241300000000000), (-7548077129168249067234270655965776934013614263/1177233628794884237219845191675000000000000000), (5577277526116210094021/8764907241300000000000), (-15058954788958392522806850348511662553197114263/2354467257589768474439690383350000000000000000)]
    bernstein := [(10067203470166201071682882202998716247019395337/376714761214362955910350461336000000000000000000000), (3350590442708493185011636399792082880101598339179/125571587071454318636783487112000000000000000000000000), (30105998096309918583579712739471868262773529142174011/1130144283643088867731051384008000000000000000000000000000), (3339295858177229382546670683082830744400501413904465579/125571587071454318636783487112000000000000000000000000000000), (196067371526030855236635665098700075904122191237262114387/7386563945379665802163734536000000000000000000000000000000000)]
    reserve := (5308757/200000000000) }

theorem tilt_039_005_valid : tilt_039_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_039_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_039_005]
  · intro i; fin_cases i <;> norm_num [tilt_039_005]
  · norm_num [tilt_039_005]
  · norm_num [tilt_039_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_039_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_039_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_039_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_039_005]

def tilt_039_006 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/20), (1001/20000)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3688541/25000000), (3688541/25000000), (9349601/100000000), (7326259/50000000), (7326259/50000000), (8050217/50000000), (15736601/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5450711/100000000), (1/100000000), (420987/10000000), (1098487/25000000), (1/100000000), (5500817/100000000), (204283/50000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-185459575095183605705285342385531062474706007/11561391364031906218243385800200000000000000000), (5578035635272623758779/8600048732100000000000), (-37737548171436933318317977661160829158272706007/5780695682015953109121692900100000000000000000), (5578035635272623758779/8600048732100000000000), (-75289636767778683030930669979936127254070706007/11561391364031906218243385800200000000000000000)]
    bernstein := [(201336378014931852599520309453024095962763368393/1849822618245104994918941728032000000000000000000000), (67092035342549330151408507007541733496916395094731/616607539415034998306313909344000000000000000000000000), (603632406196242311661433619927599112087956241171637179/5549467854735314984756825184096000000000000000000000000000), (67046822030144814754879784307390867455132630836325824331/616607539415034998306313909344000000000000000000000000000000), (67021699354945991105434722595979320205310841436384487755331/616607539415034998306313909344000000000000000000000000000000000)]
    reserve := (54347129/500000000000) }

theorem tilt_039_006_valid : tilt_039_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_039_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_039_006]
  · intro i; fin_cases i <;> norm_num [tilt_039_006]
  · norm_num [tilt_039_006]
  · norm_num [tilt_039_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_039_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_039_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_039_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_039_006]

def tilt_039_007 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/20), (1001/20000)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3688541/25000000), (3688541/25000000), (9349601/100000000), (7326259/50000000), (7326259/50000000), (8050217/50000000), (15736601/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5450711/100000000), (1/100000000), (4207789/100000000), (4391957/100000000), (1/100000000), (5500817/100000000), (208199/50000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-95731265972245158821924440011660692185603901/6059043658608013377284715225443750000000000000), (3279964867200290295411/5153279188300000000000), (-19425400819631126292907488222478281469658666401/3029521829304006688642357612721875000000000000), (3279964867200290295411/5153279188300000000000), (-2279710021958235730999591294408523661595984053/356414332859294904546159719143750000000000000)]
    bernstein := [(32785809596956974822761492319964508044069740299/969446985377282140365554436071000000000000000000000), (32747674889982763282908232891837214313493461072199/969446985377282140365554436071000000000000000000000000), (98120849817492011715508623861780232558733757562571897/2908340956131846421096663308213000000000000000000000000000), (32663634725027960537723223937147561570204425200657855599/969446985377282140365554436071000000000000000000000000000000), (1918689954591949526963164544999243371838196750884499803947/57026293257487184727385555063000000000000000000000000000000000)]
    reserve := (33645707/1000000000000) }

theorem tilt_039_007_valid : tilt_039_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_039_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_039_007]
  · intro i; fin_cases i <;> norm_num [tilt_039_007]
  · norm_num [tilt_039_007]
  · norm_num [tilt_039_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_039_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_039_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_039_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_039_007]

def tilt_039_008 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/20), (1001/20000)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3688541/25000000), (3688541/25000000), (9349601/100000000), (7326259/50000000), (7326259/50000000), (8050217/50000000), (15736601/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5450711/100000000), (1/100000000), (263247/6250000), (4391957/100000000), (1/100000000), (5500817/100000000), (204283/50000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-12982537552582951399198819453425956426520150779/809330742374899827659789556909600000000000000000), (3487125387573804575749/5377688690100000000000), (-880534840042184962509031223902672212227004383593/134888457062483304609964926151600000000000000000), (3487125387573804575749/5377688690100000000000), (-5270226502700526823654988523962607316935506150779/809330742374899827659789556909600000000000000000)]
    bernstein := [(13176048652430470154270649910411395984167928586021/129492918779983972425566329105536000000000000000000000), (13171618642544770985242378719042520336504225379558621/129492918779983972425566329105536000000000000000000000000), (13166836396546302453232368628539310715877417788876654021/129492918779983972425566329105536000000000000000000000000000), (13161701911788862930645857859430950473854163048716112912221/129492918779983972425566329105536000000000000000000000000000000), (13156215185620980563385384105422967973477155786501076016733221/129492918779983972425566329105536000000000000000000000000000000000)]
    reserve := (2031959/20000000000) }

theorem tilt_039_008_valid : tilt_039_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_039_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_039_008]
  · intro i; fin_cases i <;> norm_num [tilt_039_008]
  · norm_num [tilt_039_008]
  · norm_num [tilt_039_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_039_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_039_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_039_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_039_008]

def tilt_039_009 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/20), (1001/20000)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3688541/25000000), (3688541/25000000), (9349601/100000000), (7326259/50000000), (7326259/50000000), (8050217/50000000), (15736601/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5450711/100000000), (1/100000000), (420987/10000000), (2194983/50000000), (1/100000000), (5500817/100000000), (208199/50000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-4428529584948560907084994987329140179612871/280293784990376199188216486850000000000000000), (5577277526116210094021/8764907241300000000000), (-898580835621836285987823391767227843898112871/140146892495188099594108243425000000000000000), (5577277526116210094021/8764907241300000000000), (-1792733141658724011068561788547126547616612871/280293784990376199188216486850000000000000000)]
    bernstein := [(1195209903514796165694965561146413637123730329/44847005598460191870114637896000000000000000000000), (397790911727495937218149155989781423663278689243/14949001866153397290038212632000000000000000000000000), (3574247240705188107587881362731655185061511259386987/134541016795380575610343913688000000000000000000000000000), (396446312590523027967228643054569012611925106301958043/14949001866153397290038212632000000000000000000000000000000), (69831900405250733424243916347730156839243857189288582537/2638059152850599521771449288000000000000000000000000000000000)]
    reserve := (13235469/500000000000) }

theorem tilt_039_009_valid : tilt_039_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_039_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_039_009]
  · intro i; fin_cases i <;> norm_num [tilt_039_009]
  · norm_num [tilt_039_009]
  · norm_num [tilt_039_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_039_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_039_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_039_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_039_009]

def tilt_039_010 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/20), (1001/20000)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3688541/25000000), (3688541/25000000), (9349601/100000000), (7326259/50000000), (7326259/50000000), (8050217/50000000), (15736601/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5450711/100000000), (1/100000000), (420987/10000000), (4393949/100000000), (1/100000000), (5500817/100000000), (204283/50000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-13203383102445692564705839101951554041421611/825813856802854261877348226525000000000000000), (5578035635272623758779/8600048732100000000000), (-2695496036149761078051172139720607719501171611/412906928401427130938674113262500000000000000), (5578035635272623758779/8600048732100000000000), (-5377788689197076463537638440339263884960921611/825813856802854261877348226525000000000000000)]
    bernstein := [(21413389872115043059400829324681704219839029589/132130217088456681900375716244000000000000000000000), (7136367421962169630352755283777113686621498757663/44043405696152227300125238748000000000000000000000000), (64213365716006254050660282773407768779522816312024767/396390651265370045701127148732000000000000000000000000000), (7133149595920705741306311237226005795606405086965198463/44043405696152227300125238748000000000000000000000000000000), (7131360970153858503499402101358884789803281552867962211463/44043405696152227300125238748000000000000000000000000000000000)]
    reserve := (10119791/62500000000) }

theorem tilt_039_010_valid : tilt_039_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_039_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_039_010]
  · intro i; fin_cases i <;> norm_num [tilt_039_010]
  · norm_num [tilt_039_010]
  · norm_num [tilt_039_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_039_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_039_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_039_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_039_010]

def tilt_039_011 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/20), (1001/20000)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3688541/25000000), (3688541/25000000), (9349601/100000000), (7326259/50000000), (7326259/50000000), (8050217/50000000), (15736601/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(14653/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5450711/100000000), (1/100000000), (420987/10000000), (4391957/100000000), (1/100000000), (5500817/100000000), (208199/50000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-23256106039010712383475026309165018327357437/1472209766086145729478298696143750000000000000), (5577277526116210094021/8764907241300000000000), (-4719684738451077078616773638703391134932544937/736104883043072864739149348071875000000000000), (5577277526116210094021/8764907241300000000000), (-9416113370863143444850072251097617251537732437/1472209766086145729478298696143750000000000000)]
    bernstein := [(2318697930979496024772417258698206804625049321/78517854191261105572175930461000000000000000000000), (2315481992185226387700239467059186818171440439421/78517854191261105572175930461000000000000000000000000), (20808506462137098407624972454734370787431856097530889/706660687721349950149583374149000000000000000000000000000), (2308420773558803761740765982961836145774989679162948021/78517854191261105572175930461000000000000000000000000000000), (406689792453309458256117974779062559198070802805532971739/13856091916104900983325164199000000000000000000000000000000000)]
    reserve := (29350973/1000000000000) }

theorem tilt_039_011_valid : tilt_039_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_039_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_039_011]
  · intro i; fin_cases i <;> norm_num [tilt_039_011]
  · norm_num [tilt_039_011]
  · norm_num [tilt_039_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_039_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_039_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_039_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_039_011]

def tilt_039_012 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/20), (1001/20000)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3688541/25000000), (3688541/25000000), (9349601/100000000), (7326259/50000000), (7326259/50000000), (8050217/50000000), (15736601/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (217/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5450711/100000000), (1/100000000), (420987/10000000), (4391957/100000000), (3809/100000000), (5500817/100000000), (204283/50000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-354557884268696608848472789314215178037534096097/22008692681544821936350381112327475000000000000000), (5578035635272623758779/8600048732100000000000), (-71840104168795337986955446805662605035292534346097/11004346340772410968175190556163737500000000000000), (5578035635272623758779/8600048732100000000000), (-143325650453321979365062420822010994892547534596097/22008692681544821936350381112327475000000000000000)]
    bernstein := [(140434513966674664701941062235333564511485618006303/3521390829047171509816060977972396000000000000000000000), (46773057467258183255960983570399362604041964245672701/1173796943015723836605353659324132000000000000000000000000), (420582754740526804633724867328646560599423424617864890909/10564172487141514529448182933917188000000000000000000000000000), (46686583809975641102800220645504116031858796713348182854301/1173796943015723836605353659324132000000000000000000000000000000), (46638557292978097561763443906283331833218217757108425633005301/1173796943015723836605353659324132000000000000000000000000000000000)]
    reserve := (39733071/1000000000000) }

theorem tilt_039_012_valid : tilt_039_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_039_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_039_012]
  · intro i; fin_cases i <;> norm_num [tilt_039_012]
  · norm_num [tilt_039_012]
  · norm_num [tilt_039_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_039_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_039_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_039_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_039_012]

def tilt_039_013 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/20), (1001/20000)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3688541/25000000), (3688541/25000000), (9349601/100000000), (7326259/50000000), (7326259/50000000), (8050217/50000000), (15736601/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5450711/100000000), (1/100000000), (420987/10000000), (4391957/100000000), (1/100000000), (5498079/100000000), (208199/50000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-14412311903799673017849372909979985542530737/915585677781513387448368812915000000000000000), (5577277526116210094021/8764907241300000000000), (-2935180052761114505318501882620799553386680737/457792838890756693724184406457500000000000000), (5577277526116210094021/8764907241300000000000), (-5855947793618429337619154392331619121230830737/915585677781513387448368812915000000000000000)]
    bernstein := [(37557394508850607325534665128575991877452978989/439481125335126425975217030199200000000000000000000), (12513151836747713890749404990838733795405539787463/146493708445042141991739010066400000000000000000000000), (12506780783303230796324521847965200424474095579163663/146493708445042141991739010066400000000000000000000000000), (12500018339673828448563659933449852023307228041098908263/146493708445042141991739010066400000000000000000000000000000), (2204623147572481092294109730088268990787618804201957215517/25851830902066260351483354717600000000000000000000000000000000)]
    reserve := (85279187/1000000000000) }

theorem tilt_039_013_valid : tilt_039_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_039_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_039_013]
  · intro i; fin_cases i <;> norm_num [tilt_039_013]
  · norm_num [tilt_039_013]
  · norm_num [tilt_039_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_039_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_039_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_039_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_039_013]

def tilt_039_014 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/20), (1001/20000)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3688541/25000000), (3688541/25000000), (9349601/100000000), (7326259/50000000), (7326259/50000000), (8050217/50000000), (15736601/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5450711/100000000), (1/100000000), (420987/10000000), (4391957/100000000), (1/100000000), (1375889/25000000), (204283/50000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-32467945473285133837923904833638473629039143/2023333679160474876993798412545000000000000000), (5578035635272623758779/8600048732100000000000), (-6604376393808948657912693320353076346608589143/1011666839580237438496899206272500000000000000), (5578035635272623758779/8600048732100000000000), (-13176284842144612181987462735872514219588139143/2023333679160474876993798412545000000000000000)]
    bernstein := [(33454877524330000476228619510322262878068666457/323733388665675980319007746007200000000000000000000), (11148108338691982355173661795779321165533511970219/107911129555225326773002582002400000000000000000000000), (100298675614391111521919468898714388799603825479367371/971200165997027940957023238021600000000000000000000000000), (11140192694626236290956327750908731136516250434468660619/107911129555225326773002582002400000000000000000000000000000), (11135794548897741316216724213441199894861652975432532429619/107911129555225326773002582002400000000000000000000000000000000)]
    reserve := (25798531/250000000000) }

theorem tilt_039_014_valid : tilt_039_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_039_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_039_014]
  · intro i; fin_cases i <;> norm_num [tilt_039_014]
  · norm_num [tilt_039_014]
  · norm_num [tilt_039_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_039_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_039_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_039_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_039_014]

def tilt_039_015 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/20), (1001/20000)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3688541/25000000), (3688541/25000000), (9349601/100000000), (7326259/50000000), (7326259/50000000), (8050217/50000000), (15736601/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(14653/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5450711/100000000), (1/100000000), (420987/10000000), (4391957/100000000), (1/100000000), (5500817/100000000), (208199/50000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-23256106039010712383475026309165018327357437/1472209766086145729478298696143750000000000000), (5577277526116210094021/8764907241300000000000), (-4719684738451077078616773638703391134932544937/736104883043072864739149348071875000000000000), (5577277526116210094021/8764907241300000000000), (-9416113370863143444850072251097617251537732437/1472209766086145729478298696143750000000000000)]
    bernstein := [(2318697930979496024772417258698206804625049321/78517854191261105572175930461000000000000000000000), (2315481992185226387700239467059186818171440439421/78517854191261105572175930461000000000000000000000000), (20808506462137098407624972454734370787431856097530889/706660687721349950149583374149000000000000000000000000000), (2308420773558803761740765982961836145774989679162948021/78517854191261105572175930461000000000000000000000000000000), (406689792453309458256117974779062559198070802805532971739/13856091916104900983325164199000000000000000000000000000000000)]
    reserve := (29350973/1000000000000) }

theorem tilt_039_015_valid : tilt_039_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_039_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_039_015]
  · intro i; fin_cases i <;> norm_num [tilt_039_015]
  · norm_num [tilt_039_015]
  · norm_num [tilt_039_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_039_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_039_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_039_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_039_015]

def tilt_039_016 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/20), (1001/20000)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3688541/25000000), (3688541/25000000), (9349601/100000000), (7326259/50000000), (7326259/50000000), (8050217/50000000), (15736601/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (217/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5450711/100000000), (1/100000000), (420987/10000000), (4391957/100000000), (3809/100000000), (5500817/100000000), (204283/50000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-354557884268696608848472789314215178037534096097/22008692681544821936350381112327475000000000000000), (5578035635272623758779/8600048732100000000000), (-71840104168795337986955446805662605035292534346097/11004346340772410968175190556163737500000000000000), (5578035635272623758779/8600048732100000000000), (-143325650453321979365062420822010994892547534596097/22008692681544821936350381112327475000000000000000)]
    bernstein := [(140434513966674664701941062235333564511485618006303/3521390829047171509816060977972396000000000000000000000), (46773057467258183255960983570399362604041964245672701/1173796943015723836605353659324132000000000000000000000000), (420582754740526804633724867328646560599423424617864890909/10564172487141514529448182933917188000000000000000000000000000), (46686583809975641102800220645504116031858796713348182854301/1173796943015723836605353659324132000000000000000000000000000000), (46638557292978097561763443906283331833218217757108425633005301/1173796943015723836605353659324132000000000000000000000000000000000)]
    reserve := (39733071/1000000000000) }

theorem tilt_039_016_valid : tilt_039_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_039_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_039_016]
  · intro i; fin_cases i <;> norm_num [tilt_039_016]
  · norm_num [tilt_039_016]
  · norm_num [tilt_039_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_039_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_039_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_039_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_039_016]

def tilt_039_017 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/20), (1001/20000)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3688541/25000000), (3688541/25000000), (9349601/100000000), (7326259/50000000), (7326259/50000000), (8050217/50000000), (15736601/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5450711/100000000), (1/100000000), (420987/10000000), (4391957/100000000), (1/100000000), (5498079/100000000), (208199/50000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-14412330441600044463649105947907173888561537/915585677781513387448368812915000000000000000), (5577277526116210094021/8764907241300000000000), (-2935180071298914876764301615658726741732711537/457792838890756693724184406457500000000000000), (5577277526116210094021/8764907241300000000000), (-5855947812156229709064954125369546309576861537/915585677781513387448368812915000000000000000)]
    bernstein := [(37548451818338020757406048433386552187156966589/439481125335126425975217030199200000000000000000000), (12510170932476527085756767066160711762780110636663/146493708445042141991739010066400000000000000000000000), (37511399614787687393596662033724494483308820782278589/439481125335126425975217030199200000000000000000000000000), (12497037420527854993583997594137198367933451549940477463/146493708445042141991739010066400000000000000000000000000000), (2204097101704168940568628623453776918775102724567144998317/25851830902066260351483354717600000000000000000000000000000000)]
    reserve := (85258839/1000000000000) }

theorem tilt_039_017_valid : tilt_039_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_039_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_039_017]
  · intro i; fin_cases i <;> norm_num [tilt_039_017]
  · norm_num [tilt_039_017]
  · norm_num [tilt_039_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_039_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_039_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_039_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_039_017]

def tilt_039_018 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/20), (1001/20000)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3688541/25000000), (3688541/25000000), (9349601/100000000), (7326259/50000000), (7326259/50000000), (8050217/50000000), (15736601/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5450711/100000000), (1/100000000), (420987/10000000), (4391957/100000000), (1/100000000), (1375889/25000000), (204283/50000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-32438690226740673498161146012675742400947243/2023333679160474876993798412545000000000000000), (5578035635272623758779/8600048732100000000000), (-6604347138562404197572930561532113615380497243/1011666839580237438496899206272500000000000000), (5578035635272623758779/8600048732100000000000), (-13176255586898067721647699977051551488360047243/2023333679160474876993798412545000000000000000)]
    bernstein := [(38159150423925767570420000679950407086474278357/323733388665675980319007746007200000000000000000000), (12716203215675192829436203807751104586742870887519/107911129555225326773002582002400000000000000000000000), (114411564713091463133488598529713862604136135211803071/971200165997027940957023238021600000000000000000000000000), (12708295396441987521837720135315841130141135137123257919/107911129555225326773002582002400000000000000000000000000000), (12703901165094764707434330503234522869294823987870864326919/107911129555225326773002582002400000000000000000000000000000000)]
    reserve := (117725587/1000000000000) }

theorem tilt_039_018_valid : tilt_039_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_039_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_039_018]
  · intro i; fin_cases i <;> norm_num [tilt_039_018]
  · norm_num [tilt_039_018]
  · norm_num [tilt_039_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_039_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_039_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_039_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_039_018]

def tilt_039_019 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/20), (1001/20000)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3688541/25000000), (3688541/25000000), (9349601/100000000), (7326259/50000000), (7326259/50000000), (8050217/50000000), (15736601/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5450711/100000000), (1/100000000), (420987/10000000), (4391957/100000000), (1/100000000), (5500817/100000000), (412481/100000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-737728255844100923768979861277794231468640181/46667548376311469441519940017700000000000000000), (16902727212019/26311687500000), (-150958132917793417810776172712061444580132729181/23333774188155734720759970008850000000000000000), (16902727212019/26311687500000), (-301178537579742734697783365562845094928796818181/46667548376311469441519940017700000000000000000)]
    bernstein := [(1330654012177988213894078517760326898750590877019/7466807740209835110643190402832000000000000000000000), (443459363172534397737188962060200112076528329509473/2488935913403278370214396800944000000000000000000000000), (3990246113165143310799616662662658726040318812631387057/22400423220629505331929571208496000000000000000000000000000), (443255285546346817418073250133504817897438081842777746273/2488935913403278370214396800944000000000000000000000000000000), (443143182039332855944084986834705675163601862950102014819273/2488935913403278370214396800944000000000000000000000000000000000)]
    reserve := (35609047/200000000000) }

theorem tilt_039_019_valid : tilt_039_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_039_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_039_019]
  · intro i; fin_cases i <;> norm_num [tilt_039_019]
  · norm_num [tilt_039_019]
  · norm_num [tilt_039_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_039_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_039_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_039_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_039_019]

def tilt_039_020 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/20), (1001/20000)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(3688541/25000000), (3688541/25000000), (9349601/100000000), (7326259/50000000), (7326259/50000000), (8050217/50000000), (15736601/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5450711/100000000), (1/100000000), (420987/10000000), (4391957/100000000), (1/100000000), (5500817/100000000), (412481/100000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-744902349787279052923615617330454411404640181/46667548376311469441519940017700000000000000000), (16902727212019/26311687500000), (-150950619239967671711004310625522055203314729181/23333774188155734720759970008850000000000000000), (16902727212019/26311687500000), (-301156336130148064369085005633713655995224818181/46667548376311469441519940017700000000000000000)]
    bernstein := [(188832124979679099298545578495341049378562877019/7466807740209835110643190402832000000000000000000000), (62853076663957990575423796703386458015739253509473/2488935913403278370214396800944000000000000000000000000), (564798620677770804756893398874884904212266972547387057/22400423220629505331929571208496000000000000000000000000000), (62651018510189565840481568629258676322822509459301746273/2488935913403278370214396800944000000000000000000000000000000), (62539925251416270614133953227420556418003539951842538819273/2488935913403278370214396800944000000000000000000000000000000000)]
    reserve := (25127173/1000000000000) }

theorem tilt_039_020_valid : tilt_039_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_039_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_039_020]
  · intro i; fin_cases i <;> norm_num [tilt_039_020]
  · norm_num [tilt_039_020]
  · norm_num [tilt_039_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_039_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_039_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_039_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_039_020]

def tiltBundle039_row : Alternative → Row
  | .zero => tilt_039_000
  | (.spike 0 false false) => tilt_039_001
  | (.spike 0 false true) => tilt_039_002
  | (.spike 0 true false) => tilt_039_003
  | (.spike 0 true true) => tilt_039_004
  | (.spike 1 false false) => tilt_039_005
  | (.spike 1 false true) => tilt_039_006
  | (.spike 1 true false) => tilt_039_007
  | (.spike 1 true true) => tilt_039_008
  | (.spike 2 false false) => tilt_039_009
  | (.spike 2 false true) => tilt_039_010
  | (.spike 2 true false) => tilt_039_011
  | (.spike 2 true true) => tilt_039_012
  | (.spike 3 false false) => tilt_039_013
  | (.spike 3 false true) => tilt_039_014
  | (.spike 3 true false) => tilt_039_015
  | (.spike 3 true true) => tilt_039_016
  | (.spike 4 false false) => tilt_039_017
  | (.spike 4 false true) => tilt_039_018
  | (.spike 4 true false) => tilt_039_019
  | (.spike 4 true true) => tilt_039_020

def tiltBundle039 : TiltBundle where
  interval := ⟨(1/20), (1001/20000)⟩
  lambda := ![(3688541/25000000), (3688541/25000000), (9349601/100000000), (7326259/50000000), (7326259/50000000), (8050217/50000000), (15736601/100000000)]
  row := tiltBundle039_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_039_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_039_001_valid | exact tilt_039_002_valid | exact tilt_039_003_valid | exact tilt_039_004_valid | exact tilt_039_005_valid | exact tilt_039_006_valid | exact tilt_039_007_valid | exact tilt_039_008_valid | exact tilt_039_009_valid | exact tilt_039_010_valid | exact tilt_039_011_valid | exact tilt_039_012_valid | exact tilt_039_013_valid | exact tilt_039_014_valid | exact tilt_039_015_valid | exact tilt_039_016_valid | exact tilt_039_017_valid | exact tilt_039_018_valid | exact tilt_039_019_valid | exact tilt_039_020_valid
  same_interval := by intro a; cases a with
    | zero => rfl
    | spike i b s => fin_cases i <;> cases b <;> cases s <;> rfl
  same_lambda := by intro a; cases a with
    | zero => rfl
    | spike i b s => fin_cases i <;> cases b <;> cases s <;> rfl
  same_mode := by intro a; cases a with
    | zero => rfl
    | spike i b s => fin_cases i <;> cases b <;> cases s <;> rfl
  same_owners := by intro a; cases a with
    | zero => rfl
    | spike i b s => fin_cases i <;> cases b <;> cases s <;> rfl
  same_alternative := by intro a; cases a with
    | zero => rfl
    | spike i b s => fin_cases i <;> cases b <;> cases s <;> rfl
  same_sign := by intro a; cases a with
    | zero => rfl
    | spike i b s => fin_cases i <;> cases b <;> cases s <;> rfl

end SquaresInCircles.Eight.Generated.Owner
