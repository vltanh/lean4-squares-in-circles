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

def tilt_011_000 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(2759247/12500000), (2759247/12500000), (4837921/100000000), (1237837/20000000), (1237837/20000000), (6682713/100000000), (7988261/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(346831/6250000), 0, (193631/781250), 0, 0]] i.1) i.2
    mu := ![(2453309/25000000), (1/100000000), (1188369/20000000), (1984987/100000000), (1/100000000), (1150777/50000000), (100259/50000000)]
    alternative := .zero
    polynomial := [(-234907802763836619099093753379691078279548573/642010950425054678531163123712500000000000000), (-7533164736122978313/827393663687500000), (-16473193265419880932906744917787628200154548573/321005475212527339265581561856250000000000000), (-7533164736122978313/827393663687500000), (-32711478728075925246714396082195565322029548573/642010950425054678531163123712500000000000000)]
    bernstein := [(2955382722630850731559533836572963543964475088751/83461423555257108209051206082625000000000000000000), (454669318357932232093045265944506311855635407463/10769215942613820414071123365500000000000000000000), (13451118394598479283140913655081374631790682565629/308165256204026245694958299382000000000000000000000), (6848063923510445590782242949043488278700622481267/172307455081821126625137973848000000000000000000000), (652226938179801050824331703435573220692815390181431/21366124430145819701517108757152000000000000000000000)]
    reserve := (30526216409/1000000000000) }

theorem tilt_011_000_valid : tilt_011_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_011_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_011_000]
  · intro i; fin_cases i <;> norm_num [tilt_011_000]
  · norm_num [tilt_011_000]
  · norm_num [tilt_011_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_011_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_011_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_011_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_011_000]

def tilt_011_001 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(2759247/12500000), (2759247/12500000), (4837921/100000000), (1237837/20000000), (1237837/20000000), (6682713/100000000), (7988261/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(11037/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1379457/25000000), 0, (24790317/100000000), 0, 0]] i.1) i.2
    mu := ![(2453309/25000000), (1/100000000), (1188369/20000000), (1984987/100000000), (1/100000000), (1150777/50000000), (100259/50000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-234950564577735883497876659054992778572355323/642010950425054678531163123712500000000000000), (-602653709443157527643/66191493095000000000), (-16473251972654432786510831993251018553726855323/321005475212527339265581561856250000000000000), (-602653709443157527643/66191493095000000000), (-32711553380731129689523787327447044328881355323/642010950425054678531163123712500000000000000)]
    bernstein := [(2949737644433676876060143614021066944683951551001/83461423555257108209051206082625000000000000000000), (453942858709064319958912772128923142958414741713/10769215942613820414071123365500000000000000000000), (13430379898238250096442934342458731793515692008379/308165256204026245694958299382000000000000000000000), (6836492502394449280023284095256324775872660464517/172307455081821126625137973848000000000000000000000), (650794683066698461007859409974788775832924050473681/21366124430145819701517108757152000000000000000000000)]
    reserve := (30459182487/1000000000000) }

theorem tilt_011_001_valid : tilt_011_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_011_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_011_001]
  · intro i; fin_cases i <;> norm_num [tilt_011_001]
  · norm_num [tilt_011_001]
  · norm_num [tilt_011_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_011_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_011_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_011_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_011_001]

def tilt_011_002 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(2759247/12500000), (2759247/12500000), (4837921/100000000), (1237837/20000000), (1237837/20000000), (6682713/100000000), (7988261/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (6539/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(5580763/100000000), 0, (12389609/50000000), 0, 0]] i.1) i.2
    mu := ![(2453309/25000000), (5739/100000000), (1188369/20000000), (1984987/100000000), (1/100000000), (1150777/50000000), (100259/50000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-898493047503283752381628595914880551958172905569/2456333896326259200060230111324025000000000000000), (-6026537135567916133769/661914930950000000000), (-63026233434344813955427234555273045130497122155569/1228166948163129600030115055662012500000000000000), (-6026537135567916133769/661914930950000000000), (-125153973821186344158472840514631209709036071405569/2456333896326259200060230111324025000000000000000)]
    bernstein := [(11342433842466183886884957389643962010387459958278203/319323406522413696007829914472123250000000000000000000), (1744088189328091987646599172045041334332298714592739/41203020196440476904236117996403000000000000000000000), (51593130453688694036399052392008867384063498395775937/1179040270236604416028910453435532000000000000000000000), (26272757724595862823962471827809784740100247495021951/659248323143047630467777887942448000000000000000000000), (2504339367841770757990182022191867948195022805648582243/81746792069737906178004458104863552000000000000000000000)]
    reserve := (1531766143/50000000000) }

theorem tilt_011_002_valid : tilt_011_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_011_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_011_002]
  · intro i; fin_cases i <;> norm_num [tilt_011_002]
  · norm_num [tilt_011_002]
  · norm_num [tilt_011_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_011_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_011_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_011_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_011_002]

def tilt_011_003 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(2759247/12500000), (2759247/12500000), (4837921/100000000), (1237837/20000000), (1237837/20000000), (6682713/100000000), (7988261/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1379457/25000000), 0, (24790317/100000000), 0, 0]] i.1) i.2
    mu := ![(1226081/12500000), (1/100000000), (1188369/20000000), (1984987/100000000), (1/100000000), (1150777/50000000), (100259/50000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-58690895678822534456256696318640221415674059/160427697470661352750136043581250000000000000), (-602653709443157527643/66191493095000000000), (-4116368267081300700790588671847690471185924059/80213848735330676375068021790625000000000000), (-602653709443157527643/66191493095000000000), (-8174045638483778867124920647376740720956174059/160427697470661352750136043581250000000000000)]
    bernstein := [(739646912983650483724733746434100616029702013833/20855600671185975857517685665562500000000000000000), (113761810822017188805238129453447970378586861929/2691045247894964626776475569750000000000000000000), (3365422684071266625953880297081775774890908099707/77005294785917449320065300919000000000000000000000), (1713567712715708532120655929108259512771946827661/43056723966319434028423609116000000000000000000000), (163271607299758112934596469538695433571757047506273/5339033771823609819524527530384000000000000000000000)]
    reserve := (30580740687/1000000000000) }

theorem tilt_011_003_valid : tilt_011_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_011_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_011_003]
  · intro i; fin_cases i <;> norm_num [tilt_011_003]
  · norm_num [tilt_011_003]
  · norm_num [tilt_011_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_011_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_011_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_011_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_011_003]

def tilt_011_004 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(2759247/12500000), (2759247/12500000), (4837921/100000000), (1237837/20000000), (1237837/20000000), (6682713/100000000), (7988261/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(5580763/100000000), 0, (12389609/50000000), 0, 0]] i.1) i.2
    mu := ![(4908913/50000000), (1/100000000), (1188369/20000000), (1984987/100000000), (1/100000000), (1150777/50000000), (100259/50000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-939643186785473611161573222978098904945519817/2569244967253539148270721350725000000000000000), (-6026537135567916133769/661914930950000000000), (-65923228909581506788343640170435672001053769817/1284622483626769574135360675362500000000000000), (-6026537135567916133769/661914930950000000000), (-130906814632377539965525707117893245097162019817/2569244967253539148270721350725000000000000000)]
    bernstein := [(11883862503050512778349772302680483862342151008179/334001845742960089275193775594250000000000000000000), (56632027680793830052956671064607143533761384802437/1336007382971840357100775102377000000000000000000000), (54038398534349439062864773958404716668978036140841/1233237584281698791169946248348000000000000000000000), (853168137209015034095889752760566405302634895837833/21376118127549445713612401638032000000000000000000000), (2624544901966942209662304326333392614244356043887899/85504472510197782854449606552128000000000000000000000)]
    reserve := (30694825953/1000000000000) }

theorem tilt_011_004_valid : tilt_011_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_011_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_011_004]
  · intro i; fin_cases i <;> norm_num [tilt_011_004]
  · norm_num [tilt_011_004]
  · norm_num [tilt_011_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_011_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_011_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_011_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_011_004]

def tilt_011_005 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(2759247/12500000), (2759247/12500000), (4837921/100000000), (1237837/20000000), (1237837/20000000), (6682713/100000000), (7988261/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1379457/25000000), 0, (24790317/100000000), 0, 0]] i.1) i.2
    mu := ![(2453309/25000000), (1/100000000), (1188369/20000000), (248003/12500000), (1/100000000), (1150777/50000000), (100259/50000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-134252366421478420747964957650341856403057713/366685419503249336434837359600000000000000000), (-602653709443157527643/66191493095000000000), (-9408780098228274851384070798709951773251057713/183342709751624668217418679800000000000000000), (-602653709443157527643/66191493095000000000), (-18683307830035071282020176639769561690099057713/366685419503249336434837359600000000000000000)]
    bernstein := [(1676785229662974607369575163678091808649659505931/47669104535422413736528856748000000000000000000000), (258245340699406715730415299783314861911383896803/6150852198119021127294046032000000000000000000000), (7641522976277757369626295293829498889482501896849/176009001361559681488721932608000000000000000000000), (555478167179369409009155322023685300598675374761/14059090738557762576672105216000000000000000000000), (369681760310203262938546750715642062466338595841011/12203290761068137916551387327488000000000000000000000)]
    reserve := (30293612399/1000000000000) }

theorem tilt_011_005_valid : tilt_011_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_011_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_011_005]
  · intro i; fin_cases i <;> norm_num [tilt_011_005]
  · norm_num [tilt_011_005]
  · norm_num [tilt_011_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_011_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_011_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_011_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_011_005]

def tilt_011_006 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(2759247/12500000), (2759247/12500000), (4837921/100000000), (1237837/20000000), (1237837/20000000), (6682713/100000000), (7988261/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(5580763/100000000), 0, (12389609/50000000), 0, 0]] i.1) i.2
    mu := ![(2453309/25000000), (1/100000000), (1188369/20000000), (39719/2000000), (1/100000000), (1150777/50000000), (100259/50000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-37574909770943325051340230827939860172414629/102771586675107682928217738900000000000000000), (-6026537135567916133769/661914930950000000000), (-2636963561958804508827426960732404671325414629/51385793337553841464108869450000000000000000), (-6026537135567916133769/661914930950000000000), (-5236352214146665692603513690636869482478414629/102771586675107682928217738900000000000000000)]
    bernstein := [(476884055667766856545924815050551545511940804423/13360306267763998780668306057000000000000000000000), (73270664440638159928447445157246310550545697599/1723910486163096616860426588000000000000000000000), (2167163975660256067929678508040599697149104093317/49330361604051687805544514672000000000000000000000), (1104000638443058071809282809565610403392590667691/27582567778609545869766825408000000000000000000000), (105369704964262494621056340636640531643499259178063/3420238404547583687851086350592000000000000000000000)]
    reserve := (192548173/6250000000) }

theorem tilt_011_006_valid : tilt_011_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_011_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_011_006]
  · intro i; fin_cases i <;> norm_num [tilt_011_006]
  · norm_num [tilt_011_006]
  · norm_num [tilt_011_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_011_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_011_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_011_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_011_006]

def tilt_011_007 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(2759247/12500000), (2759247/12500000), (4837921/100000000), (1237837/20000000), (1237837/20000000), (6682713/100000000), (7988261/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1379457/25000000), 0, (24790317/100000000), 0, 0]] i.1) i.2
    mu := ![(2453309/25000000), (1/100000000), (74259/1250000), (1984987/100000000), (1/100000000), (1150777/50000000), (100259/50000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-12219986117584536407049528783416374645473524621/33378248550286115365155077656800000000000000000), (-4707323074170078481/517023130625000000), (-856454786416400267375290049142762023629138724621/16689124275143057682577538828400000000000000000), (-4707323074170078481/517023130625000000), (-1700689586715215998343530569502107672612803924621/33378248550286115365155077656800000000000000000)]
    bernstein := [(11745284859482121409034892415982976988603404941179/333782485502861153651550776568000000000000000000000), (1808826463424655262068103102276445287147286972627/43068707806820794019554938912000000000000000000000), (695804135352382192141438211948980188187654586221933/16021559304137335375274437275264000000000000000000000), (27236191609365108436456712496562507995313588702543/689099324909132704312879022592000000000000000000000), (2589771907092789499017696846532363525716378183260899/85448316288732455334796998801408000000000000000000000)]
    reserve := (6061610151/200000000000) }

theorem tilt_011_007_valid : tilt_011_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_011_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_011_007]
  · intro i; fin_cases i <;> norm_num [tilt_011_007]
  · norm_num [tilt_011_007]
  · norm_num [tilt_011_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_011_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_011_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_011_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_011_007]

def tilt_011_008 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(2759247/12500000), (2759247/12500000), (4837921/100000000), (1237837/20000000), (1237837/20000000), (6682713/100000000), (7988261/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(5580763/100000000), 0, (12389609/50000000), 0, 0]] i.1) i.2
    mu := ![(2453309/25000000), (1/100000000), (594297/10000000), (1984987/100000000), (1/100000000), (1150777/50000000), (100259/50000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-12208829436906643379084127303278242645858572671/33390890293919571202085887209300000000000000000), (-273986395230435432227/30092738850000000000), (-856757364696782418771485933915139202585938372671/16695445146959785601042943604650000000000000000), (-273986395230435432227/30092738850000000000), (-1701305899956658194163887740527000162526018172671/33390890293919571202085887209300000000000000000)]
    bernstein := [(11914266881331718539859431649668093358069440583129/333908902939195712020858872093000000000000000000000), (1830651578435347610864693441790930899524644282977/43085019734089769293014048012000000000000000000000), (703900537705542440282901743596368474844954596759583/16027627341081394177001225860464000000000000000000000), (1199224334425021141021084871252464443259603358291/29972187641105926464705424704000000000000000000000), (2632231299485325123139709180161591892466282237328849/85480679152434102277339871255808000000000000000000000)]
    reserve := (3849161187/125000000000) }

theorem tilt_011_008_valid : tilt_011_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_011_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_011_008]
  · intro i; fin_cases i <;> norm_num [tilt_011_008]
  · norm_num [tilt_011_008]
  · norm_num [tilt_011_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_011_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_011_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_011_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_011_008]

def tilt_011_009 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(2759247/12500000), (2759247/12500000), (4837921/100000000), (1237837/20000000), (1237837/20000000), (6682713/100000000), (7988261/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1379457/25000000), 0, (24790317/100000000), 0, 0]] i.1) i.2
    mu := ![(2453309/25000000), (1/100000000), (1188369/20000000), (248003/12500000), (1/100000000), (1150777/50000000), (100259/50000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-134252373306233334612951257892843152640041713/366685419503249336434837359600000000000000000), (-602653709443157527643/66191493095000000000), (-9408780105113029765249057098952453069488041713/183342709751624668217418679800000000000000000), (-602653709443157527643/66191493095000000000), (-18683307836919826195885162940012062986336041713/366685419503249336434837359600000000000000000)]
    bernstein := [(1676784316654971214992146929619267410774500313931/47669104535422413736528856748000000000000000000000), (258245223183525090968964140944060236442304000803/6150852198119021127294046032000000000000000000000), (7641519621150799460544116555552069698201800128849/176009001361559681488721932608000000000000000000000), (3888345298146144929983147505924602130133801359327/98413635169904338036704736512000000000000000000000), (52811646942951120405207425322893012074778103155573/1743327251581162559507341046784000000000000000000000)]
    reserve := (30293593411/1000000000000) }

theorem tilt_011_009_valid : tilt_011_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_011_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_011_009]
  · intro i; fin_cases i <;> norm_num [tilt_011_009]
  · norm_num [tilt_011_009]
  · norm_num [tilt_011_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_011_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_011_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_011_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_011_009]

def tilt_011_010 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(2759247/12500000), (2759247/12500000), (4837921/100000000), (1237837/20000000), (1237837/20000000), (6682713/100000000), (7988261/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(5580763/100000000), 0, (12389609/50000000), 0, 0]] i.1) i.2
    mu := ![(2453309/25000000), (1/100000000), (1188369/20000000), (39719/2000000), (1/100000000), (1150777/50000000), (100259/50000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-37573522983221731406455751743692853422770149/102771586675107682928217738900000000000000000), (-6026537135567916133769/661914930950000000000), (-2636962175171082915182542481648157664575770149/51385793337553841464108869450000000000000000), (-6026537135567916133769/661914930950000000000), (-5236350827358944098958629211552622475728770149/102771586675107682928217738900000000000000000)]
    bernstein := [(477067961747890554574990239849799851602544230663/13360306267763998780668306057000000000000000000000), (73294335520258041852980618646258468760227326719/1723910486163096616860426588000000000000000000000), (2167839794760257134110297046729440755433099598277/49330361604051687805544514672000000000000000000000), (1104377735147101537319915246633140725762667313771/27582567778609545869766825408000000000000000000000), (105416377933247566621564616885998707696841822527503/3420238404547583687851086350592000000000000000000000)]
    reserve := (7705338449/250000000000) }

theorem tilt_011_010_valid : tilt_011_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_011_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_011_010]
  · intro i; fin_cases i <;> norm_num [tilt_011_010]
  · norm_num [tilt_011_010]
  · norm_num [tilt_011_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_011_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_011_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_011_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_011_010]

def tilt_011_011 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(2759247/12500000), (2759247/12500000), (4837921/100000000), (1237837/20000000), (1237837/20000000), (6682713/100000000), (7988261/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(6189/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1379457/25000000), 0, (24790317/100000000), 0, 0]] i.1) i.2
    mu := ![(2453309/25000000), (1/100000000), (1188369/20000000), (1984987/100000000), (1/100000000), (1150777/50000000), (100259/50000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-940244186764698885088000211135129693162440417/2568043801700218714124652494850000000000000000), (-602653709443157527643/66191493095000000000), (-65893449819071486497139821547919232793780440417/1284021900850109357062326247425000000000000000), (-602653709443157527643/66191493095000000000), (-130846655451378274109191642884703335894398440417/2568043801700218714124652494850000000000000000)]
    bernstein := [(11740345119696849129281272005860343158648120980379/333845694221028432836204824330500000000000000000000), (1808228158059107191969602258288850789050095522227/43076863770455281656284493462000000000000000000000), (53506155925369766401970812987155442407610976904641/1232661024816104982779833197528000000000000000000000), (27225800382504188294583506996520463177760408368943/689229820327284506500551895392000000000000000000000), (2588305429962067951704899664540056564524008072356099/85464497720583278806068435028608000000000000000000000)]
    reserve := (30285153473/1000000000000) }

theorem tilt_011_011_valid : tilt_011_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_011_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_011_011]
  · intro i; fin_cases i <;> norm_num [tilt_011_011]
  · norm_num [tilt_011_011]
  · norm_num [tilt_011_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_011_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_011_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_011_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_011_011]

def tilt_011_012 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(2759247/12500000), (2759247/12500000), (4837921/100000000), (1237837/20000000), (1237837/20000000), (6682713/100000000), (7988261/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1833/100000000), 0, 0], ![0, 0, 0, 0, 0], ![(5580763/100000000), 0, (12389609/50000000), 0, 0]] i.1) i.2
    mu := ![(2453309/25000000), (1/100000000), (1188369/20000000), (1984987/100000000), (1609/100000000), (1150777/50000000), (100259/50000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-1510834756918287759814039802989599943121169316849/4131982476935651911026565864213650000000000000000), (-6026537135567916133769/661914930950000000000), (-106020541272786580594837960334727484738593379816849/2065991238467825955513282932106825000000000000000), (-6026537135567916133769/661914930950000000000), (-210530247788654873429861880866465369534065590316849/4131982476935651911026565864213650000000000000000)]
    bernstein := [(19157853750151943567712805932270619528415059601703563/537157722001634748433453562347774500000000000000000000), (2943887536893667349000464942788568961258404874204419/69310673806662548184961749980358000000000000000000000), (87074919562425565682668592294773227644829437055927377/1983351588929112917292751614822552000000000000000000000), (27566872442269153280739663527460191221637473952519/689229820327284506500551895392000000000000000000000), (2630519571364852849489563518714026087212148022469467/85464497720583278806068435028608000000000000000000000)]
    reserve := (30779091219/1000000000000) }

theorem tilt_011_012_valid : tilt_011_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_011_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_011_012]
  · intro i; fin_cases i <;> norm_num [tilt_011_012]
  · norm_num [tilt_011_012]
  · norm_num [tilt_011_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_011_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_011_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_011_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_011_012]

def tilt_011_013 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(2759247/12500000), (2759247/12500000), (4837921/100000000), (1237837/20000000), (1237837/20000000), (6682713/100000000), (7988261/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1379457/25000000), 0, (24790317/100000000), 0, 0]] i.1) i.2
    mu := ![(2453309/25000000), (1/100000000), (1188369/20000000), (1984987/100000000), (1/100000000), (2300407/100000000), (100259/50000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-234929279765383937628203014807066345011475517/641690998531622007511375952043750000000000000), (-602653709443157527643/66191493095000000000), (-16465138185248153445781965012775342155766225517/320845499265811003755687976021875000000000000), (-602653709443157527643/66191493095000000000), (-32695347090730922953935727010743617966520975517/641690998531622007511375952043750000000000000)]
    bernstein := [(2935562641018603822383597004589914827019311264079/83419829809110860976478873765687500000000000000000), (452081338378438314986248178997072470582384525327/10763849007627207867932757905250000000000000000000), (13376998433544722454281383429590389380279095476941/308011679295178563605460456981000000000000000000000), (6807034110853223843114269252228536363623125816843/172221584122035325886924126484000000000000000000000), (647245996386938872405885593290361317952261823455799/21355476431132380409978591684016000000000000000000000)]
    reserve := (30308197453/1000000000000) }

theorem tilt_011_013_valid : tilt_011_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_011_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_011_013]
  · intro i; fin_cases i <;> norm_num [tilt_011_013]
  · norm_num [tilt_011_013]
  · norm_num [tilt_011_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_011_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_011_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_011_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_011_013]

def tilt_011_014 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(2759247/12500000), (2759247/12500000), (4837921/100000000), (1237837/20000000), (1237837/20000000), (6682713/100000000), (7988261/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(5580763/100000000), 0, (12389609/50000000), 0, 0]] i.1) i.2
    mu := ![(2453309/25000000), (1/100000000), (1188369/20000000), (1984987/100000000), (1/100000000), (1151351/50000000), (100259/50000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-1878775881396237218544069430884426540764629981/5138649450121697803703293991100000000000000000), (-6026537135567916133769/661914930950000000000), (-131849981935112040459333239005287193301711629981/2569324725060848901851646995550000000000000000), (-6026537135567916133769/661914930950000000000), (-261821187988827843700122408579689960062658629981/5138649450121697803703293991100000000000000000)]
    bernstein := [(23843897272817139772248429350157250730287162329647/668024428515820714481428218843000000000000000000000), (3663502010585662622623581813476421218753739854311/86196700453654285739539125012000000000000000000000), (108357359027233469747097355716417258452429357249213/2466551736058414945777581115728000000000000000000000), (55199491548345280363512686143001611965174601936499/1379147207258468571832626000192000000000000000000000), (5268397031372911674986838115696306654111341310063607/171014253700050102907245624023808000000000000000000000)]
    reserve := (30806771467/1000000000000) }

theorem tilt_011_014_valid : tilt_011_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_011_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_011_014]
  · intro i; fin_cases i <;> norm_num [tilt_011_014]
  · norm_num [tilt_011_014]
  · norm_num [tilt_011_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_011_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_011_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_011_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_011_014]

def tilt_011_015 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(2759247/12500000), (2759247/12500000), (4837921/100000000), (1237837/20000000), (1237837/20000000), (6682713/100000000), (7988261/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(6189/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1379457/25000000), 0, (24790317/100000000), 0, 0]] i.1) i.2
    mu := ![(2453309/25000000), (1/100000000), (1188369/20000000), (1984987/100000000), (1/100000000), (1150777/50000000), (100259/50000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-940244186764698885088000211135129693162440417/2568043801700218714124652494850000000000000000), (-602653709443157527643/66191493095000000000), (-65893449819071486497139821547919232793780440417/1284021900850109357062326247425000000000000000), (-602653709443157527643/66191493095000000000), (-130846655451378274109191642884703335894398440417/2568043801700218714124652494850000000000000000)]
    bernstein := [(11740345119696849129281272005860343158648120980379/333845694221028432836204824330500000000000000000000), (1808228158059107191969602258288850789050095522227/43076863770455281656284493462000000000000000000000), (53506155925369766401970812987155442407610976904641/1232661024816104982779833197528000000000000000000000), (27225800382504188294583506996520463177760408368943/689229820327284506500551895392000000000000000000000), (2588305429962067951704899664540056564524008072356099/85464497720583278806068435028608000000000000000000000)]
    reserve := (30285153473/1000000000000) }

theorem tilt_011_015_valid : tilt_011_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_011_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_011_015]
  · intro i; fin_cases i <;> norm_num [tilt_011_015]
  · norm_num [tilt_011_015]
  · norm_num [tilt_011_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_011_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_011_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_011_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_011_015]

def tilt_011_016 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(2759247/12500000), (2759247/12500000), (4837921/100000000), (1237837/20000000), (1237837/20000000), (6682713/100000000), (7988261/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1833/100000000), 0, 0], ![0, 0, 0, 0, 0], ![(5580763/100000000), 0, (12389609/50000000), 0, 0]] i.1) i.2
    mu := ![(2453309/25000000), (1/100000000), (1188369/20000000), (1984987/100000000), (1609/100000000), (1150777/50000000), (100259/50000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-1510834756918287759814039802989599943121169316849/4131982476935651911026565864213650000000000000000), (-6026537135567916133769/661914930950000000000), (-106020541272786580594837960334727484738593379816849/2065991238467825955513282932106825000000000000000), (-6026537135567916133769/661914930950000000000), (-210530247788654873429861880866465369534065590316849/4131982476935651911026565864213650000000000000000)]
    bernstein := [(19157853750151943567712805932270619528415059601703563/537157722001634748433453562347774500000000000000000000), (2943887536893667349000464942788568961258404874204419/69310673806662548184961749980358000000000000000000000), (87074919562425565682668592294773227644829437055927377/1983351588929112917292751614822552000000000000000000000), (27566872442269153280739663527460191221637473952519/689229820327284506500551895392000000000000000000000), (2630519571364852849489563518714026087212148022469467/85464497720583278806068435028608000000000000000000000)]
    reserve := (30779091219/1000000000000) }

theorem tilt_011_016_valid : tilt_011_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_011_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_011_016]
  · intro i; fin_cases i <;> norm_num [tilt_011_016]
  · norm_num [tilt_011_016]
  · norm_num [tilt_011_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_011_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_011_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_011_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_011_016]

def tilt_011_017 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(2759247/12500000), (2759247/12500000), (4837921/100000000), (1237837/20000000), (1237837/20000000), (6682713/100000000), (7988261/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1379457/25000000), 0, (24790317/100000000), 0, 0]] i.1) i.2
    mu := ![(2453309/25000000), (1/100000000), (1188369/20000000), (1984987/100000000), (1/100000000), (2300407/100000000), (100259/50000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-234929284195505691251409348765479454832175267/641690998531622007511375952043750000000000000), (-602653709443157527643/66191493095000000000), (-16465138189678275199405171346733755265586925267/320845499265811003755687976021875000000000000), (-602653709443157527643/66191493095000000000), (-32695347095161044707558933344702031076341675267/641690998531622007511375952043750000000000000)]
    bernstein := [(2935562053526867709149335439362877094366855317329/83419829809110860976478873765687500000000000000000), (452081262760690102391739264660919099052860492577/10763849007627207867932757905250000000000000000000), (13376996274626778626345110320638803810686948408691/308011679295178563605460456981000000000000000000000), (6807032906210086476138379715922885128068629097093/172221584122035325886924126484000000000000000000000), (647245847289184409062485111450684945797862960219049/21355476431132380409978591684016000000000000000000000)]
    reserve := (30308190471/1000000000000) }

theorem tilt_011_017_valid : tilt_011_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_011_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_011_017]
  · intro i; fin_cases i <;> norm_num [tilt_011_017]
  · norm_num [tilt_011_017]
  · norm_num [tilt_011_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_011_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_011_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_011_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_011_017]

def tilt_011_018 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(2759247/12500000), (2759247/12500000), (4837921/100000000), (1237837/20000000), (1237837/20000000), (6682713/100000000), (7988261/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(5580763/100000000), 0, (12389609/50000000), 0, 0]] i.1) i.2
    mu := ![(2453309/25000000), (1/100000000), (1188369/20000000), (1984987/100000000), (1/100000000), (1151351/50000000), (100259/50000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-1878750556163353050916983441758963023322227981/5138649450121697803703293991100000000000000000), (-6026537135567916133769/661914930950000000000), (-131849956609879156291706153016161729784269227981/2569324725060848901851646995550000000000000000), (-6026537135567916133769/661914930950000000000), (-261821162663594959532495322590564496545216227981/5138649450121697803703293991100000000000000000)]
    bernstein := [(23847255727925607893779183626052344168876418755647/668024428515820714481428218843000000000000000000000), (3663934286985762479850312561858957997978099592311/86196700453654285739539125012000000000000000000000), (108369700696999212504302289538962018017082796703213/2466551736058414945777581115728000000000000000000000), (55206378010996376108837535391986777091629996178499/1379147207258468571832626000192000000000000000000000), (5269249363557958833004352149666855168608782028169607/171014253700050102907245624023808000000000000000000000)]
    reserve := (616235109/20000000000) }

theorem tilt_011_018_valid : tilt_011_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_011_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_011_018]
  · intro i; fin_cases i <;> norm_num [tilt_011_018]
  · norm_num [tilt_011_018]
  · norm_num [tilt_011_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_011_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_011_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_011_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_011_018]

def tilt_011_019 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(2759247/12500000), (2759247/12500000), (4837921/100000000), (1237837/20000000), (1237837/20000000), (6682713/100000000), (7988261/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(5524511/100000000), 0, (24790317/100000000), 0, 0]] i.1) i.2
    mu := ![(2453309/25000000), (1/100000000), (1188369/20000000), (1984987/100000000), (1/100000000), (1150777/50000000), (100259/50000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-1880469528549874395576425415995965433733033959/5136087603400437428249304989700000000000000000), (-6026537397152852867617/661914930950000000000), (-131786880791988976187807079016730415910230552959/2568043801700218714124652494850000000000000000), (-6026537397152852867617/661914930950000000000), (-261693292055428077980037732617464866386728071959/5136087603400437428249304989700000000000000000)]
    bernstein := [(23483220173419719751127506238460404418033142701133/667691388442056865672409648661000000000000000000000), (3616781707343665791006468413066365682231190631829/86153727540910563312568986924000000000000000000000), (107021594922399337406487910619310158067322735136407/2465322049632209965559666395056000000000000000000000), (54456776669497004910316463159202301033948130636761/1378459640654569013001103790784000000000000000000000), (5177250992639552970542946147856103036739231836857573/170928995441166557612136870057216000000000000000000000)]
    reserve := (15144449247/500000000000) }

theorem tilt_011_019_valid : tilt_011_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_011_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_011_019]
  · intro i; fin_cases i <;> norm_num [tilt_011_019]
  · norm_num [tilt_011_019]
  · norm_num [tilt_011_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_011_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_011_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_011_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_011_019]

def tilt_011_020 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(2759247/12500000), (2759247/12500000), (4837921/100000000), (1237837/20000000), (1237837/20000000), (6682713/100000000), (7988261/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(5574081/100000000), 0, (12389609/50000000), 0, 0]] i.1) i.2
    mu := ![(2453309/25000000), (1/100000000), (1188369/20000000), (1984987/100000000), (1/100000000), (1150777/50000000), (100259/50000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-2003966006287358182227126945918510001820207/5481416865955642933030208100000000000000000), (-3013268943812304621791/330957465475000000000), (-131784125741695651864797883687832443848899052959/2568043801700218714124652494850000000000000000), (-3013268943812304621791/330957465475000000000), (-261690535335500049112848949427339243826092571959/5136087603400437428249304989700000000000000000)]
    bernstein := [(23848408597118894983001607245406404899925004201133/667691388442056865672409648661000000000000000000000), (3663785692898216326510627006912868786270165131829/86153727540910563312568986924000000000000000000000), (108363564978907935464120208646924342551755693636407/2465322049632209965559666395056000000000000000000000), (55205568140109135249401477717986539656023501136761/1378459640654569013001103790784000000000000000000000), (5269927447286876081530583586694728791146778218357573/170928995441166557612136870057216000000000000000000000)]
    reserve := (2408679/78125000) }

theorem tilt_011_020_valid : tilt_011_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_011_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_011_020]
  · intro i; fin_cases i <;> norm_num [tilt_011_020]
  · norm_num [tilt_011_020]
  · norm_num [tilt_011_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_011_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_011_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_011_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_011_020]

def tiltBundle011_row : Alternative → Row
  | .zero => tilt_011_000
  | (.spike 0 false false) => tilt_011_001
  | (.spike 0 false true) => tilt_011_002
  | (.spike 0 true false) => tilt_011_003
  | (.spike 0 true true) => tilt_011_004
  | (.spike 1 false false) => tilt_011_005
  | (.spike 1 false true) => tilt_011_006
  | (.spike 1 true false) => tilt_011_007
  | (.spike 1 true true) => tilt_011_008
  | (.spike 2 false false) => tilt_011_009
  | (.spike 2 false true) => tilt_011_010
  | (.spike 2 true false) => tilt_011_011
  | (.spike 2 true true) => tilt_011_012
  | (.spike 3 false false) => tilt_011_013
  | (.spike 3 false true) => tilt_011_014
  | (.spike 3 true false) => tilt_011_015
  | (.spike 3 true true) => tilt_011_016
  | (.spike 4 false false) => tilt_011_017
  | (.spike 4 false true) => tilt_011_018
  | (.spike 4 true false) => tilt_011_019
  | (.spike 4 true true) => tilt_011_020

def tiltBundle011 : TiltBundle where
  interval := ⟨(-1/10), (-3/40)⟩
  lambda := ![(2759247/12500000), (2759247/12500000), (4837921/100000000), (1237837/20000000), (1237837/20000000), (6682713/100000000), (7988261/25000000)]
  row := tiltBundle011_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_011_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_011_001_valid | exact tilt_011_002_valid | exact tilt_011_003_valid | exact tilt_011_004_valid | exact tilt_011_005_valid | exact tilt_011_006_valid | exact tilt_011_007_valid | exact tilt_011_008_valid | exact tilt_011_009_valid | exact tilt_011_010_valid | exact tilt_011_011_valid | exact tilt_011_012_valid | exact tilt_011_013_valid | exact tilt_011_014_valid | exact tilt_011_015_valid | exact tilt_011_016_valid | exact tilt_011_017_valid | exact tilt_011_018_valid | exact tilt_011_019_valid | exact tilt_011_020_valid
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
