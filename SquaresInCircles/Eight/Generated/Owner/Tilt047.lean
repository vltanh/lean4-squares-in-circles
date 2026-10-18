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

def tilt_047_000 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(17/160), (9/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22246331/100000000), (22246331/100000000), (14855919/100000000), (20325709/100000000), (20325709/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (5561583/50000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (2032571/20000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(496853/12500000), (1/100000000), (3034047/50000000), (3180767/50000000), (1/100000000), (3631661/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-90522298146477958924191197434229242291963/1741355250554446861562081700000000000000000), (110163230461063/202269800000000), (-477909951070699542966403662906656242291963/870677625277223430781040850000000000000000), (110163230461063/202269800000000), (-865297603994921127008616128379083242291963/1741355250554446861562081700000000000000000)]
    bernstein := [(316228591507390065908044211745156012273943159877/1141214577003362295193325862912000000000000000000000), (554023221540800322635915000617723875759550224029/570607288501681147596662931456000000000000000000000), (1422619415284082153356866030069740773119757955999/855910932752521721394994397184000000000000000000000), (335323768683312682708633957965811258670069334541/142651822125420286899165732864000000000000000000000), (216585099444672321254969199933033794200210712357/71325911062710143449582866432000000000000000000000)]
    reserve := (11083931/40000000000) }

theorem tilt_047_000_valid : tilt_047_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_047_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_047_000]
  · intro i; fin_cases i <;> norm_num [tilt_047_000]
  · norm_num [tilt_047_000]
  · norm_num [tilt_047_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_047_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_047_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_047_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_047_000]

def tilt_047_001 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(17/160), (9/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22246331/100000000), (22246331/100000000), (14855919/100000000), (20325709/100000000), (20325709/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (5561583/50000000), 0], ![(11123/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (2032571/20000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(496853/12500000), (1/100000000), (3034047/50000000), (3180767/50000000), (1/100000000), (3631661/100000000), (1/100000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-90102634910314644669622219847006825126213/1741355250554446861562081700000000000000000), (110163230461063/202269800000000), (-477490287834536228711834685319433825126213/870677625277223430781040850000000000000000), (110163230461063/202269800000000), (-864877940758757812754047150791860825126213/1741355250554446861562081700000000000000000)]
    bernstein := [(597503813625388620314231466446914391842133365627/1141214577003362295193325862912000000000000000000000), (694753182222728372202269186185025675386680191779/570607288501681147596662931456000000000000000000000), (1633855657548085269860882065027777641253786681249/855910932752521721394994397184000000000000000000000), (370553822960402399933692534066150513310396474291/142651822125420286899165732864000000000000000000000), (234212365851668264846075864930045969705804798107/71325911062710143449582866432000000000000000000000)]
    reserve := (130892083/250000000000) }

theorem tilt_047_001_valid : tilt_047_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_047_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_047_001]
  · intro i; fin_cases i <;> norm_num [tilt_047_001]
  · norm_num [tilt_047_001]
  · norm_num [tilt_047_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_047_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_047_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_047_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_047_001]

def tilt_047_002 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(17/160), (9/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22246331/100000000), (22246331/100000000), (14855919/100000000), (20325709/100000000), (20325709/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (5561583/50000000), 0], ![0, 0, (659/10000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (2032571/20000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(496853/12500000), (5783/100000000), (3034047/50000000), (3180767/50000000), (1/100000000), (3631661/100000000), (1/100000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-105099005879219167700183010018778871248487311/2014051482791273240082703694220000000000000000), (110163230461063/202269800000000), (-553151565251373851803405947584187939448487311/1007025741395636620041351847110000000000000000), (110163230461063/202269800000000), (-1001204124623528535906628885149597007648487311/2014051482791273240082703694220000000000000000)]
    bernstein := [(97040025629291610174595971020260465440025510933169/1319928779762088830620600693044019200000000000000000000), (506340052242806046187550265751653844273371407513513/659964389881044415310300346522009600000000000000000000), (1443601818064931214179157451031207373740230960925603/989946584821566622965450519783014400000000000000000000), (354179230110797417966274040561234704088527360658777/164991097470261103827575086630502400000000000000000000), (233662513133443737330298746129621042503810372147729/82495548735130551913787543315251200000000000000000000)]
    reserve := (73519137/1000000000000) }

theorem tilt_047_002_valid : tilt_047_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_047_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_047_002]
  · intro i; fin_cases i <;> norm_num [tilt_047_002]
  · norm_num [tilt_047_002]
  · norm_num [tilt_047_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_047_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_047_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_047_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_047_002]

def tilt_047_003 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(17/160), (9/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22246331/100000000), (22246331/100000000), (14855919/100000000), (20325709/100000000), (20325709/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11134289/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (2032571/20000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(79417/2000000), (1/100000000), (3034047/50000000), (3180767/50000000), (1/100000000), (3631661/100000000), (1/100000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-3595612113657148669890629089757190628649/69584570251806120927455325000000000000000), (110163230461063/202269800000000), (-19075625936801471809672610566382940628649/34792285125903060463727662500000000000000), (110163230461063/202269800000000), (-34555639759945794949454592043008690628649/69584570251806120927455325000000000000000)]
    bernstein := [(27153681918516351124397599533627958924602443671/45602943960223659411017121792000000000000000000000), (29402131268033706492543444391884136425477923167/22801471980111829705508560896000000000000000000000), (67750214586862280318839550839601099581764823477/34202207970167744558262841344000000000000000000000), (15217835142478864893076764752585889338256688943/5700367995027957426377140224000000000000000000000), (9564521345908685931118441969549546977539110711/2850183997513978713188570112000000000000000000000)]
    reserve := (297718519/500000000000) }

theorem tilt_047_003_valid : tilt_047_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_047_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_047_003]
  · intro i; fin_cases i <;> norm_num [tilt_047_003]
  · norm_num [tilt_047_003]
  · norm_num [tilt_047_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_047_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_047_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_047_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_047_003]

def tilt_047_004 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(17/160), (9/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22246331/100000000), (22246331/100000000), (14855919/100000000), (20325709/100000000), (20325709/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (5556021/50000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (2032571/20000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3978799/100000000), (1/100000000), (3034047/50000000), (3180767/50000000), (1/100000000), (3631661/100000000), (1/100000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-3883106958149622557197799161729559529167/74570981087055861338175300000000000000000), (110163230461063/202269800000000), (-20472414240723467625389305759972559529167/37285490543527930669087650000000000000000), (110163230461063/202269800000000), (-37061721523297312693580812358215559529167/74570981087055861338175300000000000000000)]
    bernstein := [(9103365446887921821388014556486531816501057393/48870838165212929286586564608000000000000000000000), (21504443679350728248286340490699829802720390761/24435419082606464643293282304000000000000000000000), (57588176625960980068311301584471142552270763491/36653128623909696964939923456000000000000000000000), (13803800548034685017721110228798582720593721369/6108854770651616160823320576000000000000000000000), (8996771965976153805510945652130328439408469713/3054427385325808080411660288000000000000000000000)]
    reserve := (93136989/500000000000) }

theorem tilt_047_004_valid : tilt_047_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_047_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_047_004]
  · intro i; fin_cases i <;> norm_num [tilt_047_004]
  · norm_num [tilt_047_004]
  · norm_num [tilt_047_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_047_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_047_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_047_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_047_004]

def tilt_047_005 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(17/160), (9/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22246331/100000000), (22246331/100000000), (14855919/100000000), (20325709/100000000), (20325709/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (5561583/50000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (2032571/20000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(496853/12500000), (1/100000000), (3034047/50000000), (794813/12500000), (1/100000000), (3631661/100000000), (1/100000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-90066155235114845722728224959586621091223/1740525842677481970076705200000000000000000), (110163230461063/202269800000000), (-477269295337686747251313017645798621091223/870262921338740985038352600000000000000000), (110163230461063/202269800000000), (-864472435440258648779897810332010621091223/1740525842677481970076705200000000000000000)]
    bernstein := [(592905402233199858756080876042472466969326197417/1140671016257114583909469519872000000000000000000000), (692263944700729163895460619022935558524502384609/570335508128557291954734759936000000000000000000000), (1629837795012361559116339295542244924109407155979/855503262192835937932102139904000000000000000000000), (369837017013091994278227937401229048819922745361/142583877032139322988683689984000000000000000000000), (233830467201265584757595933046535739911146399497/71291938516069661494341844992000000000000000000000)]
    reserve := (259893253/500000000000) }

theorem tilt_047_005_valid : tilt_047_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_047_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_047_005]
  · intro i; fin_cases i <;> norm_num [tilt_047_005]
  · norm_num [tilt_047_005]
  · norm_num [tilt_047_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_047_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_047_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_047_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_047_005]

def tilt_047_006 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(17/160), (9/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22246331/100000000), (22246331/100000000), (14855919/100000000), (20325709/100000000), (20325709/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (5561583/50000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (2032571/20000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(496853/12500000), (1/100000000), (3034047/50000000), (1272913/20000000), (1/100000000), (3631661/100000000), (1/100000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-36288054653627566716973598879114426147021/696873972865353739488486300000000000000000), (110163230461063/202269800000000), (-191316945310104343924459968066767426147021/348436986432676869744243150000000000000000), (110163230461063/202269800000000), (-346345835966581121131946337254420426147021/696873972865353739488486300000000000000000)]
    bernstein := [(85074963068019492007751127755912808903851766259/456703326857038226711174381568000000000000000000000), (200962887503471709269331579973990450015503956443/228351663428519113355587190784000000000000000000000), (538170074157843327499435419469451476523914743433/342527495142778670033380786176000000000000000000000), (128998403560008954230258333467797698672405312747/57087915857129778338896797696000000000000000000000), (84076006954466133183660230956474255132837862419/28543957928564889169448398848000000000000000000000)]
    reserve := (37256117/200000000000) }

theorem tilt_047_006_valid : tilt_047_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_047_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_047_006]
  · intro i; fin_cases i <;> norm_num [tilt_047_006]
  · norm_num [tilt_047_006]
  · norm_num [tilt_047_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_047_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_047_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_047_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_047_006]

def tilt_047_007 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(17/160), (9/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22246331/100000000), (22246331/100000000), (14855919/100000000), (20325709/100000000), (20325709/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (5561583/50000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (2032571/20000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(496853/12500000), (1/100000000), (3032347/50000000), (3180767/50000000), (1/100000000), (3631661/100000000), (1/100000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-45026747559597546994486330022587297285069/870189777869793262483605850000000000000000), (330489691383189/606469400000000), (-238849146665505453983616119917054944660069/435094888934896631241802925000000000000000), (330489691383189/606469400000000), (-432671545771413360972745909811522592035069/870189777869793262483605850000000000000000)]
    bernstein := [(313295700772312300506940896673738436781710182851/570287572824747712501255929856000000000000000000000), (354625285771706203535345528971964800150489930027/285143786412373856250627964928000000000000000000000), (275921783752350084009684690858034078114179703379/142571893206186928125313982464000000000000000000000), (187077125477178036161006714674917513644357805883/71285946603093464062656991232000000000000000000000), (118003209871442918580140290710038294673672133091/35642973301546732031328495616000000000000000000000)]
    reserve := (274682209/500000000000) }

theorem tilt_047_007_valid : tilt_047_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_047_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_047_007]
  · intro i; fin_cases i <;> norm_num [tilt_047_007]
  · norm_num [tilt_047_007]
  · norm_num [tilt_047_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_047_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_047_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_047_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_047_007]

def tilt_047_008 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(17/160), (9/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22246331/100000000), (22246331/100000000), (14855919/100000000), (20325709/100000000), (20325709/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (5561583/50000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (2032571/20000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(496853/12500000), (1/100000000), (3035747/50000000), (3180767/50000000), (1/100000000), (3631661/100000000), (1/100000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-4124219925121868719350649439172453470979/79196861153150327188952350000000000000000), (25422283952553/46703800000000), (-21721061181332202996903619946259667345979/39598430576575163594476175000000000000000), (25422283952553/46703800000000), (-39317902437542537274456590453346881220979/79196861153150327188952350000000000000000)]
    bernstein := [(8134724435135785947900270540835168887763105741/51902454925328598426551812096000000000000000000000), (22063717363731411176276432106253629030677187557/25951227462664299213275906048000000000000000000000), (59986543237689535674197775780127909313690320567/38926841193996448819913859072000000000000000000000), (203696565437616929082425817673032795689226243/91377561488254574694633472000000000000000000000), (9455076620597652712591447710294415456698289581/3243903432833037401659488256000000000000000000000)]
    reserve := (78365507/500000000000) }

theorem tilt_047_008_valid : tilt_047_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_047_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_047_008]
  · intro i; fin_cases i <;> norm_num [tilt_047_008]
  · norm_num [tilt_047_008]
  · norm_num [tilt_047_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_047_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_047_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_047_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_047_008]

def tilt_047_009 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(17/160), (9/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22246331/100000000), (22246331/100000000), (14855919/100000000), (20325709/100000000), (20325709/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (5561583/50000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (2032571/20000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(496853/12500000), (1/100000000), (3034047/50000000), (1271701/20000000), (1/100000000), (3631661/100000000), (1/100000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-36026520435842149213929087340640908216337/696210446563781826300185100000000000000000), (110163230461063/202269800000000), (-190907800834999180410513318299321908216337/348105223281890913150092550000000000000000), (110163230461063/202269800000000), (-345789081234156211607097549258002908216337/696210446563781826300185100000000000000000)]
    bernstein := [(237126892662539430879448077213552645428751675823/456268478260040057684089307136000000000000000000000), (276887957072887429764186408979526275132467474871/228134239130020028842044653568000000000000000000000), (651908706264129238281560966849939150852898219901/342201358695030043263066980352000000000000000000000), (147930408011610387508671437541356394842012503559/57033559782505007210511163392000000000000000000000), (93529989024373579193926865878062482859330891343/28516779891252503605255581696000000000000000000000)]
    reserve := (519709127/1000000000000) }

theorem tilt_047_009_valid : tilt_047_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_047_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_047_009]
  · intro i; fin_cases i <;> norm_num [tilt_047_009]
  · norm_num [tilt_047_009]
  · norm_num [tilt_047_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_047_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_047_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_047_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_047_009]

def tilt_047_010 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(17/160), (9/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22246331/100000000), (22246331/100000000), (14855919/100000000), (20325709/100000000), (20325709/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (5561583/50000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (2032571/20000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(496853/12500000), (1/100000000), (3034047/50000000), (3182283/50000000), (1/100000000), (3631661/100000000), (1/100000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-3020832956854831024498561473783858561343/58072840196511898146499110000000000000000), (110163230461063/202269800000000), (-15939909208071918340551618396437958561343/29036420098255949073249555000000000000000), (110163230461063/202269800000000), (-28858985459289005656604675319092058561343/58072840196511898146499110000000000000000)]
    bernstein := [(9215632424770840161413634537385947702669488897/38058616551186037569289656729600000000000000000000), (17810633486049082982996381541061768545530568569/19029308275593018784644828364800000000000000000000), (46444166612139118502059737908503063128103822739/28543962413389528176967242547200000000000000000000), (11016159061817353794055043392504522186363228201/4757327068898254696161207091200000000000000000000), (7139572730354921112927202904909567906769326177/2378663534449127348080603545600000000000000000000)]
    reserve := (242143127/1000000000000) }

theorem tilt_047_010_valid : tilt_047_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_047_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_047_010]
  · intro i; fin_cases i <;> norm_num [tilt_047_010]
  · norm_num [tilt_047_010]
  · norm_num [tilt_047_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_047_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_047_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_047_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_047_010]

def tilt_047_011 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(17/160), (9/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22246331/100000000), (22246331/100000000), (14855919/100000000), (20325709/100000000), (20325709/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (5561583/50000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(10163/50000000), 0, 0, 0, 0], ![0, 0, 0, (2032571/20000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(496853/12500000), (1/100000000), (3034047/50000000), (3180767/50000000), (1/100000000), (3631661/100000000), (1/100000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-90138854991213880579856116357205343386213/1741355250554446861562081700000000000000000), (110163230461063/202269800000000), (-477526507915435464622068581829632343386213/870677625277223430781040850000000000000000), (110163230461063/202269800000000), (-864914160839657048664281047302059343386213/1741355250554446861562081700000000000000000)]
    bernstein := [(573227654976838775184337484370679739535371905627/1141214577003362295193325862912000000000000000000000), (682607132434221046930241809699511848999817771779/570607288501681147596662931456000000000000000000000), (1615624387509755387873011381993678295277573661249/855910932752521721394994397184000000000000000000000), (367513205374581550341664667906676794402240294291/142651822125420286899165732864000000000000000000000), (232691000718208454284357915375537425565932938107/71325911062710143449582866432000000000000000000000)]
    reserve := (12557403/25000000000) }

theorem tilt_047_011_valid : tilt_047_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_047_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_047_011]
  · intro i; fin_cases i <;> norm_num [tilt_047_011]
  · norm_num [tilt_047_011]
  · norm_num [tilt_047_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_047_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_047_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_047_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_047_011]

def tilt_047_012 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(17/160), (9/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22246331/100000000), (22246331/100000000), (14855919/100000000), (20325709/100000000), (20325709/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (5561583/50000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6021/100000000), 0, 0], ![0, 0, 0, (2032571/20000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(496853/12500000), (1/100000000), (3034047/50000000), (3180767/50000000), (1321/25000000), (3631661/100000000), (1/100000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-239996635426300036142104185451621668155947127/4600660571964848608247019851400000000000000000), (110163230461063/202269800000000), (-1263474814452093461181629519229773802155947127/2300330285982424304123509925700000000000000000), (110163230461063/202269800000000), (-2286952993477886886221154853007925936155947127/4600660571964848608247019851400000000000000000)]
    bernstein := [(274669961866086103516359661507014793682411540492233/3015088912442883183900766929813504000000000000000000000), (1183142236368557701243895291373634005256964591293441/1507544456221441591950383464906752000000000000000000000), (3337398096634467453511348380685812022276805255358571/2261316684332162387925575197360128000000000000000000000), (815683784904858154907326631688821337710661295383089/376886114055360397987595866226688000000000000000000000), (537072624125568959843223851055186929310880527706153/188443057027680198993797933113344000000000000000000000)]
    reserve := (91098461/1000000000000) }

theorem tilt_047_012_valid : tilt_047_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_047_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_047_012]
  · intro i; fin_cases i <;> norm_num [tilt_047_012]
  · norm_num [tilt_047_012]
  · norm_num [tilt_047_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_047_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_047_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_047_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_047_012]

def tilt_047_013 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(17/160), (9/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22246331/100000000), (22246331/100000000), (14855919/100000000), (20325709/100000000), (20325709/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (5561583/50000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (10173017/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(496853/12500000), (1/100000000), (3034047/50000000), (3180767/50000000), (1/100000000), (3628029/100000000), (1/100000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-29979008367374549466138409607587011032383/579871244251945991352737100000000000000000), (110163230461063/202269800000000), (-158979084737480928643699682433388011032383/289935622125972995676368550000000000000000), (110163230461063/202269800000000), (-287979161107587307821260955259189011032383/579871244251945991352737100000000000000000)]
    bernstein := [(215836189635943577937305006521274338863076685057/380024418632955324892929785856000000000000000000000), (239792045205655108545278875302392265015290752889/190012209316477662446464892928000000000000000000000), (556741242355586830514478052085530152679816224659/285018313974716493669697339392000000000000000000000), (125507078113460369309687944404291103102176189481/47503052329119415611616223232000000000000000000000), (79049777801010834789487998680623912493834160737/23751526164559707805808111616000000000000000000000)]
    reserve := (141988369/250000000000) }

theorem tilt_047_013_valid : tilt_047_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_047_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_047_013]
  · intro i; fin_cases i <;> norm_num [tilt_047_013]
  · norm_num [tilt_047_013]
  · norm_num [tilt_047_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_047_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_047_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_047_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_047_013]

def tilt_047_014 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(17/160), (9/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22246331/100000000), (22246331/100000000), (14855919/100000000), (20325709/100000000), (20325709/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (5561583/50000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (2538173/25000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(496853/12500000), (1/100000000), (3034047/50000000), (3180767/50000000), (1/100000000), (908823/25000000), (1/100000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-5041902223162816369236546170293700218231/96838682714459432692731800000000000000000), (110163230461063/202269800000000), (-26584956115861246626783875340551700218231/48419341357229716346365900000000000000000), (110163230461063/202269800000000), (-48128010008559676884331204510809700218231/96838682714459432692731800000000000000000)]
    bernstein := [(12319367784758276247165518354580886859084507849/63464199103748133809508712448000000000000000000000), (28174886044134392072777892484187157653469103873/31732099551874066904754356224000000000000000000000), (75158353407962782123588767948455892592174950763/47598149327811100357131534336000000000000000000000), (17988094580676854429082516990093678607758247217/7933024887968516726188589056000000000000000000000), (11714491984891496032331946080191402391864525609/3966512443984258363094294528000000000000000000000)]
    reserve := (6066101/31250000000) }

theorem tilt_047_014_valid : tilt_047_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_047_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_047_014]
  · intro i; fin_cases i <;> norm_num [tilt_047_014]
  · norm_num [tilt_047_014]
  · norm_num [tilt_047_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_047_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_047_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_047_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_047_014]

def tilt_047_015 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(17/160), (9/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22246331/100000000), (22246331/100000000), (14855919/100000000), (20325709/100000000), (20325709/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (5561583/50000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(10163/50000000), 0, 0, 0, 0], ![0, 0, 0, (2032571/20000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(496853/12500000), (1/100000000), (3034047/50000000), (3180767/50000000), (1/100000000), (3631661/100000000), (1/100000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-90138854991213880579856116357205343386213/1741355250554446861562081700000000000000000), (110163230461063/202269800000000), (-477526507915435464622068581829632343386213/870677625277223430781040850000000000000000), (110163230461063/202269800000000), (-864914160839657048664281047302059343386213/1741355250554446861562081700000000000000000)]
    bernstein := [(573227654976838775184337484370679739535371905627/1141214577003362295193325862912000000000000000000000), (682607132434221046930241809699511848999817771779/570607288501681147596662931456000000000000000000000), (1615624387509755387873011381993678295277573661249/855910932752521721394994397184000000000000000000000), (367513205374581550341664667906676794402240294291/142651822125420286899165732864000000000000000000000), (232691000718208454284357915375537425565932938107/71325911062710143449582866432000000000000000000000)]
    reserve := (12557403/25000000000) }

theorem tilt_047_015_valid : tilt_047_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_047_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_047_015]
  · intro i; fin_cases i <;> norm_num [tilt_047_015]
  · norm_num [tilt_047_015]
  · norm_num [tilt_047_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_047_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_047_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_047_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_047_015]

def tilt_047_016 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(17/160), (9/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22246331/100000000), (22246331/100000000), (14855919/100000000), (20325709/100000000), (20325709/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (5561583/50000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6021/100000000), 0, 0], ![0, 0, 0, (2032571/20000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(496853/12500000), (1/100000000), (3034047/50000000), (3180767/50000000), (1321/25000000), (3631661/100000000), (1/100000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-239996635426300036142104185451621668155947127/4600660571964848608247019851400000000000000000), (110163230461063/202269800000000), (-1263474814452093461181629519229773802155947127/2300330285982424304123509925700000000000000000), (110163230461063/202269800000000), (-2286952993477886886221154853007925936155947127/4600660571964848608247019851400000000000000000)]
    bernstein := [(274669961866086103516359661507014793682411540492233/3015088912442883183900766929813504000000000000000000000), (1183142236368557701243895291373634005256964591293441/1507544456221441591950383464906752000000000000000000000), (3337398096634467453511348380685812022276805255358571/2261316684332162387925575197360128000000000000000000000), (815683784904858154907326631688821337710661295383089/376886114055360397987595866226688000000000000000000000), (537072624125568959843223851055186929310880527706153/188443057027680198993797933113344000000000000000000000)]
    reserve := (91098461/1000000000000) }

theorem tilt_047_016_valid : tilt_047_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_047_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_047_016]
  · intro i; fin_cases i <;> norm_num [tilt_047_016]
  · norm_num [tilt_047_016]
  · norm_num [tilt_047_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_047_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_047_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_047_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_047_016]

def tilt_047_017 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(17/160), (9/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22246331/100000000), (22246331/100000000), (14855919/100000000), (20325709/100000000), (20325709/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (5561583/50000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (2032571/20000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(496853/12500000), (1/100000000), (3034047/50000000), (3180767/50000000), (1/100000000), (3631661/100000000), (1/100000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-90522298146477958924191197434229242291963/1741355250554446861562081700000000000000000), (110163230461063/202269800000000), (-477909951070699542966403662906656242291963/870677625277223430781040850000000000000000), (110163230461063/202269800000000), (-865297603994921127008616128379083242291963/1741355250554446861562081700000000000000000)]
    bernstein := [(316228591507390065908044211745156012273943159877/1141214577003362295193325862912000000000000000000000), (554023221540800322635915000617723875759550224029/570607288501681147596662931456000000000000000000000), (1422619415284082153356866030069740773119757955999/855910932752521721394994397184000000000000000000000), (335323768683312682708633957965811258670069334541/142651822125420286899165732864000000000000000000000), (216585099444672321254969199933033794200210712357/71325911062710143449582866432000000000000000000000)]
    reserve := (11083931/40000000000) }

theorem tilt_047_017_valid : tilt_047_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_047_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_047_017]
  · intro i; fin_cases i <;> norm_num [tilt_047_017]
  · norm_num [tilt_047_017]
  · norm_num [tilt_047_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_047_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_047_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_047_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_047_017]

def tilt_047_018 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(17/160), (9/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22246331/100000000), (22246331/100000000), (14855919/100000000), (20325709/100000000), (20325709/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (5561583/50000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (2032571/20000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(496853/12500000), (1/100000000), (3034047/50000000), (3180767/50000000), (1/100000000), (3631661/100000000), (1/100000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-90522298146477958924191197434229242291963/1741355250554446861562081700000000000000000), (110163230461063/202269800000000), (-477909951070699542966403662906656242291963/870677625277223430781040850000000000000000), (110163230461063/202269800000000), (-865297603994921127008616128379083242291963/1741355250554446861562081700000000000000000)]
    bernstein := [(316228591507390065908044211745156012273943159877/1141214577003362295193325862912000000000000000000000), (554023221540800322635915000617723875759550224029/570607288501681147596662931456000000000000000000000), (1422619415284082153356866030069740773119757955999/855910932752521721394994397184000000000000000000000), (335323768683312682708633957965811258670069334541/142651822125420286899165732864000000000000000000000), (216585099444672321254969199933033794200210712357/71325911062710143449582866432000000000000000000000)]
    reserve := (11083931/40000000000) }

theorem tilt_047_018_valid : tilt_047_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_047_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_047_018]
  · intro i; fin_cases i <;> norm_num [tilt_047_018]
  · norm_num [tilt_047_018]
  · norm_num [tilt_047_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_047_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_047_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_047_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_047_018]

def tilt_047_019 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(17/160), (9/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22246331/100000000), (22246331/100000000), (14855919/100000000), (20325709/100000000), (20325709/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (5561583/50000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (2032571/20000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(496853/12500000), (1/100000000), (3034047/50000000), (3180767/50000000), (1/100000000), (3631661/100000000), (1/100000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-90522298146477958924191197434229242291963/1741355250554446861562081700000000000000000), (110163230461063/202269800000000), (-477909951070699542966403662906656242291963/870677625277223430781040850000000000000000), (110163230461063/202269800000000), (-865297603994921127008616128379083242291963/1741355250554446861562081700000000000000000)]
    bernstein := [(316228591507390065908044211745156012273943159877/1141214577003362295193325862912000000000000000000000), (554023221540800322635915000617723875759550224029/570607288501681147596662931456000000000000000000000), (1422619415284082153356866030069740773119757955999/855910932752521721394994397184000000000000000000000), (335323768683312682708633957965811258670069334541/142651822125420286899165732864000000000000000000000), (216585099444672321254969199933033794200210712357/71325911062710143449582866432000000000000000000000)]
    reserve := (11083931/40000000000) }

theorem tilt_047_019_valid : tilt_047_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_047_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_047_019]
  · intro i; fin_cases i <;> norm_num [tilt_047_019]
  · norm_num [tilt_047_019]
  · norm_num [tilt_047_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_047_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_047_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_047_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_047_019]

def tilt_047_020 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(17/160), (9/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(22246331/100000000), (22246331/100000000), (14855919/100000000), (20325709/100000000), (20325709/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (5561583/50000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (2032571/20000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(496853/12500000), (1/100000000), (3034047/50000000), (3180767/50000000), (1/100000000), (3631661/100000000), (1/100000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-90522298146477958924191197434229242291963/1741355250554446861562081700000000000000000), (110163230461063/202269800000000), (-477909951070699542966403662906656242291963/870677625277223430781040850000000000000000), (110163230461063/202269800000000), (-865297603994921127008616128379083242291963/1741355250554446861562081700000000000000000)]
    bernstein := [(316228591507390065908044211745156012273943159877/1141214577003362295193325862912000000000000000000000), (554023221540800322635915000617723875759550224029/570607288501681147596662931456000000000000000000000), (1422619415284082153356866030069740773119757955999/855910932752521721394994397184000000000000000000000), (335323768683312682708633957965811258670069334541/142651822125420286899165732864000000000000000000000), (216585099444672321254969199933033794200210712357/71325911062710143449582866432000000000000000000000)]
    reserve := (11083931/40000000000) }

theorem tilt_047_020_valid : tilt_047_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_047_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_047_020]
  · intro i; fin_cases i <;> norm_num [tilt_047_020]
  · norm_num [tilt_047_020]
  · norm_num [tilt_047_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_047_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_047_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_047_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_047_020]

def tiltBundle047_row : Alternative → Row
  | .zero => tilt_047_000
  | (.spike 0 false false) => tilt_047_001
  | (.spike 0 false true) => tilt_047_002
  | (.spike 0 true false) => tilt_047_003
  | (.spike 0 true true) => tilt_047_004
  | (.spike 1 false false) => tilt_047_005
  | (.spike 1 false true) => tilt_047_006
  | (.spike 1 true false) => tilt_047_007
  | (.spike 1 true true) => tilt_047_008
  | (.spike 2 false false) => tilt_047_009
  | (.spike 2 false true) => tilt_047_010
  | (.spike 2 true false) => tilt_047_011
  | (.spike 2 true true) => tilt_047_012
  | (.spike 3 false false) => tilt_047_013
  | (.spike 3 false true) => tilt_047_014
  | (.spike 3 true false) => tilt_047_015
  | (.spike 3 true true) => tilt_047_016
  | (.spike 4 false false) => tilt_047_017
  | (.spike 4 false true) => tilt_047_018
  | (.spike 4 true false) => tilt_047_019
  | (.spike 4 true true) => tilt_047_020

def tiltBundle047 : TiltBundle where
  interval := ⟨(17/160), (9/80)⟩
  lambda := ![(22246331/100000000), (22246331/100000000), (14855919/100000000), (20325709/100000000), (20325709/100000000), 0, 0]
  row := tiltBundle047_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_047_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_047_001_valid | exact tilt_047_002_valid | exact tilt_047_003_valid | exact tilt_047_004_valid | exact tilt_047_005_valid | exact tilt_047_006_valid | exact tilt_047_007_valid | exact tilt_047_008_valid | exact tilt_047_009_valid | exact tilt_047_010_valid | exact tilt_047_011_valid | exact tilt_047_012_valid | exact tilt_047_013_valid | exact tilt_047_014_valid | exact tilt_047_015_valid | exact tilt_047_016_valid | exact tilt_047_017_valid | exact tilt_047_018_valid | exact tilt_047_019_valid | exact tilt_047_020_valid
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
