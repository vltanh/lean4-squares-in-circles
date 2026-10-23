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

def tilt_045_000 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(19/200), (1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7720253/50000000), (7720253/50000000), (10308351/100000000), (1832147/12500000), (1832147/12500000), (3760517/25000000), (1806777/12500000)]
    cone := fun i => (![![0, 0, 0, (98629/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5341387/100000000), (1/100000000), (2131869/50000000), (2263921/50000000), (1/100000000), (2653453/50000000), (151241/20000000)]
    alternative := .zero
    polynomial := [(-1587930723644081961645968620672374761242232857/47025571955310705741098389890450000000000000000), (47070689250737/71062300000000), (-76452020544964815626891993956242420023842232857/23512785977655352870549194945225000000000000000), (47070689250737/71062300000000), (-151316110366285549292138019291812465286442232857/47025571955310705741098389890450000000000000000)]
    bernstein := [(9049052536187520661726096311340226767268205661682903/75240915128497129185757423824720000000000000000000000000), (231542433495453754919252373518230353461595440253279/1254015252141618819762623730412000000000000000000000000), (132909280254952712789576589509337432131657963134169/564306863463728468893180678685400000000000000000000000), (855575377394357532311286228464559683278356011139/3135038130354047049406559326030000000000000000000000), (139554951328169794397296172000897188377782625743/470255719553107057410983898904500000000000000000000)]
    reserve := (120267709/1000000000000) }

theorem tilt_045_000_valid : tilt_045_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_045_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_045_000]
  · intro i; fin_cases i <;> norm_num [tilt_045_000]
  · norm_num [tilt_045_000]
  · norm_num [tilt_045_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_045_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_045_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_045_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_045_000]

def tilt_045_001 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(19/200), (1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7720253/50000000), (7720253/50000000), (10308351/100000000), (1832147/12500000), (1832147/12500000), (3760517/25000000), (1806777/12500000)]
    cone := fun i => (![![0, 0, 0, (98629/20000000), 0], ![(15441/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5341387/100000000), (1/100000000), (2131869/50000000), (2263921/50000000), (1/100000000), (2653453/50000000), (4749/625000)]
    alternative := (.spike 0 false false)
    polynomial := [(-8267340258904358141030226726463626070192873/246102182626592151559956464175000000000000000), (370955082748327701431/562458104500000000000), (-398401832393440728723332129873670374863192873/123051091313296075779978232087500000000000000), (370955082748327701431/562458104500000000000), (-788536324527977099305634033020877123656192873/246102182626592151559956464175000000000000000)]
    bernstein := [(57501190632694979718222408112181646218882586357767/393763492202547442495930342680000000000000000000000000), (1378622309435646442001538527715284207015115391031/6562724870042457374932172378000000000000000000000000), (769838928017406708691691312527783643587552537241/2953226191519105818719477570100000000000000000000000), (4886578311500730024783656049066283324280218571/16406812175106143437330430945000000000000000000000), (791298441160502211318284147459936417803002527/2461021826265921515599564641750000000000000000000)]
    reserve := (73014883/500000000000) }

theorem tilt_045_001_valid : tilt_045_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_045_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_045_001]
  · intro i; fin_cases i <;> norm_num [tilt_045_001]
  · norm_num [tilt_045_001]
  · norm_num [tilt_045_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_045_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_045_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_045_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_045_001]

def tilt_045_002 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(19/200), (1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7720253/50000000), (7720253/50000000), (10308351/100000000), (1832147/12500000), (1832147/12500000), (3760517/25000000), (1806777/12500000)]
    cone := fun i => (![![0, 0, 0, (98629/20000000), 0], ![0, 0, (2287/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5341387/100000000), (2007/50000000), (2131869/50000000), (2263921/50000000), (1/100000000), (2653453/50000000), (75257/10000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-106180822558716552040545312762780280580062753097/3130888212218521559801635776307170000000000000000), (317665117730961489577/477494242062500000000), (-5111800887774281513797593963465456767961615553097/1565444106109260779900817888153585000000000000000), (317665117730961489577/477494242062500000000), (-10117420952989846475554642614168133255343168353097/3130888212218521559801635776307170000000000000000)]
    bernstein := [(621874570031491347429590753859326971404423517918685863/5009421139549634495682617242091472000000000000000000000000), (15768412834400855467610091432861774523935341182384559/83490352325827241594710287368191200000000000000000000000), (9018620630998766311866946180857823757417105655370249/37570658546622258717619629315686040000000000000000000000), (57955017765335072766177562676693995108968353737619/208725880814568103986775718420478000000000000000000000), (9445747459230718193811529422882807942088002857503/31308882122185215598016357763071700000000000000000000)]
    reserve := (31035251/250000000000) }

theorem tilt_045_002_valid : tilt_045_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_045_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_045_002]
  · intro i; fin_cases i <;> norm_num [tilt_045_002]
  · norm_num [tilt_045_002]
  · norm_num [tilt_045_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_045_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_045_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_045_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_045_002]

def tilt_045_003 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(19/200), (1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7720253/50000000), (7720253/50000000), (10308351/100000000), (1832147/12500000), (1832147/12500000), (3760517/25000000), (1806777/12500000)]
    cone := fun i => (![![0, 0, 0, (100173/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1334657/25000000), (1/100000000), (2131869/50000000), (2263921/50000000), (1/100000000), (2653453/50000000), (4749/625000)]
    alternative := (.spike 0 true false)
    polynomial := [(-1031384304619898495749339646115388914301051/30746882856256212218339245462500000000000000), (370955082748327701431/562458104500000000000), (-49773006178189807280889164858999375575801051/15373441428128106109169622731250000000000000), (370955082748327701431/562458104500000000000), (-98514628051759716066028990071883362237301051/30746882856256212218339245462500000000000000)]
    bernstein := [(9626529633003106730258820691495267717279221852629/49195012570009939549342792740000000000000000000000000), (212967830985612114950853185747654213898752273897/819916876166832325822379879000000000000000000000000), (114517012904733740095587116919189977576784853667/368962594275074546620070945550000000000000000000000), (712427806507486150651392886686687657379222877/2049792190417080814555949697500000000000000000000), (114156939936546421776836884034510654887728749/307468828562562122183392454625000000000000000000)]
    reserve := (195681007/1000000000000) }

theorem tilt_045_003_valid : tilt_045_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_045_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_045_003]
  · intro i; fin_cases i <;> norm_num [tilt_045_003]
  · norm_num [tilt_045_003]
  · norm_num [tilt_045_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_045_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_045_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_045_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_045_003]

def tilt_045_004 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(19/200), (1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7720253/50000000), (7720253/50000000), (10308351/100000000), (1832147/12500000), (1832147/12500000), (3760517/25000000), (1806777/12500000)]
    cone := fun i => (![![0, 0, 0, (19417/4000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2672073/50000000), (1/100000000), (2131869/50000000), (2263921/50000000), (1/100000000), (2653453/50000000), (75257/10000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-132032884375037513835687554162377560727833871/3901974860171130974220011472450000000000000000), (317665117730961489577/477494242062500000000), (-6370455443767292739915389514443818664635833871/1950987430085565487110005736225000000000000000), (317665117730961489577/477494242062500000000), (-12608878003159547965995091474725259768543833871/3901974860171130974220011472450000000000000000)]
    bernstein := [(1261358724204536028473845553879839378115076671617409/6243159776273809558752018355920000000000000000000000000), (27761174461450184126643013489462420455516868218937/104052662937896825979200305932000000000000000000000000), (14890673898152137151811721164809168384512561942607/46823698322053571690640137669400000000000000000000000), (92521129420585690668721646426059297918898286517/260131657344742064948000764830000000000000000000000), (14817499022000134907002580084712654365958681929/39019748601711309742200114724500000000000000000000)]
    reserve := (101019257/500000000000) }

theorem tilt_045_004_valid : tilt_045_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_045_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_045_004]
  · intro i; fin_cases i <;> norm_num [tilt_045_004]
  · norm_num [tilt_045_004]
  · norm_num [tilt_045_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_045_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_045_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_045_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_045_004]

def tilt_045_005 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(19/200), (1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7720253/50000000), (7720253/50000000), (10308351/100000000), (1832147/12500000), (1832147/12500000), (3760517/25000000), (1806777/12500000)]
    cone := fun i => (![![0, 0, 0, (98629/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5341387/100000000), (1/100000000), (2131869/50000000), (282857/6250000), (1/100000000), (2653453/50000000), (4749/625000)]
    alternative := (.spike 1 false false)
    polynomial := [(-363596712560405414826715576255450241508332777/10823402064412102554486530743200000000000000000), (370955082748327701431/562458104500000000000), (-17521439127855767341844909071220747038020332777/5411701032206051277243265371600000000000000000), (370955082748327701431/562458104500000000000), (-34679281543151129268863102566186043834532332777/10823402064412102554486530743200000000000000000)]
    bernstein := [(2520939411977028247997185704171138762571153740408583/17317443303059364087178449189120000000000000000000000000), (60498737539575470766858055903410808007604209989519/288624055050989401452974153152000000000000000000000000), (33797500936696154505946771641684450026951477168809/129880824772945230653838368918400000000000000000000000), (214577709929167609904203813327872776190740148979/721560137627473503632435382880000000000000000000000), (34751139513016928318535172597956971662249341823/108234020644121025544865307432000000000000000000000)]
    reserve := (145572263/1000000000000) }

theorem tilt_045_005_valid : tilt_045_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_045_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_045_005]
  · intro i; fin_cases i <;> norm_num [tilt_045_005]
  · norm_num [tilt_045_005]
  · norm_num [tilt_045_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_045_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_045_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_045_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_045_005]

def tilt_045_006 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(19/200), (1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7720253/50000000), (7720253/50000000), (10308351/100000000), (1832147/12500000), (1832147/12500000), (3760517/25000000), (1806777/12500000)]
    cone := fun i => (![![0, 0, 0, (98629/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5341387/100000000), (1/100000000), (2131869/50000000), (4529973/100000000), (1/100000000), (2653453/50000000), (75257/10000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-138322584320761179473696427769940750443136753/4087595699927483046534668261825000000000000000), (317665117730961489577/477494242062500000000), (-6673513133186576309725093091653388474301136753/2043797849963741523267334130912500000000000000), (317665117730961489577/477494242062500000000), (-13208703682052391439976489755536836198159136753/4087595699927483046534668261825000000000000000)]
    bernstein := [(1307086469907529911588400874044609456266088352572287/6540153119883972874455469218920000000000000000000000000), (86531250303641918527891899387867205836388636065173/327007655994198643722773460946000000000000000000000000), (15491863801836475446085513340892817254019067537201/49051148399129796558416019141900000000000000000000000), (288980246984156707822487286611835566438721464993/817519139985496609306933652365000000000000000000000), (15432982548149848823141834995996848728953982647/40875956999274830465346682618250000000000000000000)]
    reserve := (199855637/1000000000000) }

theorem tilt_045_006_valid : tilt_045_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_045_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_045_006]
  · intro i; fin_cases i <;> norm_num [tilt_045_006]
  · norm_num [tilt_045_006]
  · norm_num [tilt_045_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_045_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_045_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_045_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_045_006]

def tilt_045_007 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(19/200), (1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7720253/50000000), (7720253/50000000), (10308351/100000000), (1832147/12500000), (1832147/12500000), (3760517/25000000), (1806777/12500000)]
    cone := fun i => (![![0, 0, 0, (98629/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5341387/100000000), (1/100000000), (4261397/100000000), (2263921/50000000), (1/100000000), (2653453/50000000), (4749/625000)]
    alternative := (.spike 1 true false)
    polynomial := [(-49576723591600722107220801635424490702555021/1475802363191751343372145000325000000000000000), (2225200153628803429509/3372895725500000000000), (-2389374070525120649863731139893888082676305021/737901181595875671686072500162500000000000000), (2225200153628803429509/3372895725500000000000), (-4729171417458640577620241478152351674650055021/1475802363191751343372145000325000000000000000)]
    bernstein := [(383338986558371066568987194042541911593279103128259/2361283781106802149395432000520000000000000000000000000), (8916021790496994451668059322397278848889116037987/39354729685113369156590533342000000000000000000000000), (4911509814529618142065289141742300075219598372157/17709628358301016120465740003900000000000000000000000), (30959075723790388264252452520300782630904182567/98386824212783422891476333355000000000000000000000), (4996030824060455643167334697789762076122230779/14758023631917513433721450003250000000000000000000)]
    reserve := (162343463/1000000000000) }

theorem tilt_045_007_valid : tilt_045_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_045_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_045_007]
  · intro i; fin_cases i <;> norm_num [tilt_045_007]
  · norm_num [tilt_045_007]
  · norm_num [tilt_045_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_045_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_045_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_045_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_045_007]

def tilt_045_008 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(19/200), (1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7720253/50000000), (7720253/50000000), (10308351/100000000), (1832147/12500000), (1832147/12500000), (3760517/25000000), (1806777/12500000)]
    cone := fun i => (![![0, 0, 0, (98629/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5341387/100000000), (1/100000000), (4266079/100000000), (2263921/50000000), (1/100000000), (2653453/50000000), (75257/10000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-792285147393340782194917267764366014134666953/23412610033361068804214404549075000000000000000), (476612495539679366349/716634614515625000000), (-38219669387694295096506108975235775726284916953/11706305016680534402107202274537500000000000000), (476612495539679366349/716634614515625000000), (-75647053627995249410817300682707185438435166953/23412610033361068804214404549075000000000000000)]
    bernstein := [(6858942064684555188284565218228352968466860844878087/37460176053377710086743047278520000000000000000000000000), (463918562396088250734859499663870379752664653523373/1873008802668885504337152363926000000000000000000000000), (83928609142599935539648605448503761817672673210601/280951320400332825650572854588900000000000000000000000), (1574326654459807477727254597286976487930089111193/4682522006672213760842880909815000000000000000000000), (84312705678642298317550291824755205401159912447/234126100333610688042144045490750000000000000000000)]
    reserve := (11443723/62500000000) }

theorem tilt_045_008_valid : tilt_045_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_045_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_045_008]
  · intro i; fin_cases i <;> norm_num [tilt_045_008]
  · norm_num [tilt_045_008]
  · norm_num [tilt_045_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_045_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_045_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_045_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_045_008]

def tilt_045_009 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(19/200), (1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7720253/50000000), (7720253/50000000), (10308351/100000000), (1832147/12500000), (1832147/12500000), (3760517/25000000), (1806777/12500000)]
    cone := fun i => (![![0, 0, 0, (98629/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5341387/100000000), (1/100000000), (2131869/50000000), (282857/6250000), (1/100000000), (2653453/50000000), (4749/625000)]
    alternative := (.spike 2 false false)
    polynomial := [(-355075548522685980817596855674822045666423/10569728578527443900865752678906250000000000), (370955082748327701431/562458104500000000000), (-17110781032209562862671301440601869698510173/5284864289263721950432876339453125000000000), (370955082748327701431/562458104500000000000), (-33866486515896439744525006025528917351353923/10569728578527443900865752678906250000000000)]
    bernstein := [(2460822243827555841481475129741407889801749473217/16911565725643910241385204286250000000000000000000000), (236254317727094353149127325498889898050676850899/1127437715042927349425680285750000000000000000000000), (65995239542895819134793196698291439461265933307/253673485884658653620778064293750000000000000000000), (838021823560507334481571647094065774651808309/2818594287607318373564200714375000000000000000000), (8482548283758496601041969884573380111653963/26424321446318609752164381697265625000000000000)]
    reserve := (145511201/1000000000000) }

theorem tilt_045_009_valid : tilt_045_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_045_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_045_009]
  · intro i; fin_cases i <;> norm_num [tilt_045_009]
  · norm_num [tilt_045_009]
  · norm_num [tilt_045_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_045_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_045_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_045_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_045_009]

def tilt_045_010 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(19/200), (1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7720253/50000000), (7720253/50000000), (10308351/100000000), (1832147/12500000), (1832147/12500000), (3760517/25000000), (1806777/12500000)]
    cone := fun i => (![![0, 0, 0, (98629/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5341387/100000000), (1/100000000), (2131869/50000000), (4529973/100000000), (1/100000000), (2653453/50000000), (75257/10000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-118410057306416148986044632045548150043756949/3503653457080699754172572795850000000000000000), (317665117730961489577/477494242062500000000), (-5720001956334257689201527486802789056207756949/1751826728540349877086286397925000000000000000), (317665117730961489577/477494242062500000000), (-11321593855362099229417010341560029962371756949/3503653457080699754172572795850000000000000000)]
    bernstein := [(1368226499778290223836663487248240464795770695529371/5605845531329119606676116473360000000000000000000000000), (28856270239585959603538949769125585996295484889603/93430758855485326777935274556000000000000000000000000), (15139506296511815773621018535138898015269275157333/42043841484968397050070873550200000000000000000000000), (92908408736533866377070837690922298805058905623/233576897138713316944838186390000000000000000000000), (14780432735164270451346503940931130545971363251/35036534570806997541725727958500000000000000000000)]
    reserve := (61017847/250000000000) }

theorem tilt_045_010_valid : tilt_045_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_045_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_045_010]
  · intro i; fin_cases i <;> norm_num [tilt_045_010]
  · norm_num [tilt_045_010]
  · norm_num [tilt_045_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_045_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_045_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_045_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_045_010]

def tilt_045_011 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(19/200), (1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7720253/50000000), (7720253/50000000), (10308351/100000000), (1832147/12500000), (1832147/12500000), (3760517/25000000), (1806777/12500000)]
    cone := fun i => (![![0, 0, 0, (98629/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(14657/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5341387/100000000), (1/100000000), (2131869/50000000), (2263921/50000000), (1/100000000), (2653453/50000000), (4749/625000)]
    alternative := (.spike 2 true false)
    polynomial := [(-8269430355689139087649833094955208427379123/246102182626592151559956464175000000000000000), (370955082748327701431/562458104500000000000), (-398403922490225509669951736242161957220379123/123051091313296075779978232087500000000000000), (370955082748327701431/562458104500000000000), (-788538414624761880252253639389368706013379123/246102182626592151559956464175000000000000000)]
    bernstein := [(54096401398397901950733572882064784740972817071517/393763492202547442495930342680000000000000000000000000), (1321849108705190473677661861877751743135794394781/6562724870042457374932172378000000000000000000000000), (744278751948608897567293644278789037985536203491/2953226191519105818719477570100000000000000000000000), (4744508162748814740209152363587955759259247321/16406812175106143437330430945000000000000000000000), (769977363858951774851679582477304792146066277/2461021826265921515599564641750000000000000000000)]
    reserve := (68691489/500000000000) }

theorem tilt_045_011_valid : tilt_045_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_045_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_045_011]
  · intro i; fin_cases i <;> norm_num [tilt_045_011]
  · norm_num [tilt_045_011]
  · norm_num [tilt_045_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_045_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_045_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_045_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_045_011]

def tilt_045_012 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(19/200), (1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7720253/50000000), (7720253/50000000), (10308351/100000000), (1832147/12500000), (1832147/12500000), (3760517/25000000), (1806777/12500000)]
    cone := fun i => (![![0, 0, 0, (98629/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2171/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5341387/100000000), (1/100000000), (2131869/50000000), (2263921/50000000), (3811/100000000), (2653453/50000000), (75257/10000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-755925758259356557080664781285598189405188925001/22294123648663650344551632928824037500000000000000), (317665117730961489577/477494242062500000000), (-36399457276451654892760994392324275493984967925001/11147061824331825172275816464412018750000000000000), (317665117730961489577/477494242062500000000), (-72042988794643953228441324003362952798564746925001/22294123648663650344551632928824037500000000000000)]
    bernstein := [(4682789593953007268187447687609785597674870788078064679/35670597837861840551282612686118460000000000000000000000000), (116527604321080717709799320589664026791084409638812047/594509963964364009188043544768641000000000000000000000000), (66130271959221440933556968810521514661349225396495817/267529483783963804134619595145888450000000000000000000000), (423304265397191598806763950527758420648413863407027/1486274909910910022970108861921602500000000000000000000), (68854720692942569230093281342707338265005872064799/222941236486636503445516329288240375000000000000000000)]
    reserve := (16409837/125000000000) }

theorem tilt_045_012_valid : tilt_045_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_045_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_045_012]
  · intro i; fin_cases i <;> norm_num [tilt_045_012]
  · norm_num [tilt_045_012]
  · norm_num [tilt_045_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_045_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_045_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_045_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_045_012]

def tilt_045_013 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(19/200), (1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7720253/50000000), (7720253/50000000), (10308351/100000000), (1832147/12500000), (1832147/12500000), (3760517/25000000), (1806777/12500000)]
    cone := fun i => (![![0, 0, 0, (98629/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5341387/100000000), (1/100000000), (2131869/50000000), (2263921/50000000), (1/100000000), (2652127/50000000), (4749/625000)]
    alternative := (.spike 3 false false)
    polynomial := [(-3631439616951281746583324794395617463149369/108230847523315100656281143583000000000000000), (370955082748327701431/562458104500000000000), (-175204833567161923501860159837172134305429369/54115423761657550328140571791500000000000000), (370955082748327701431/562458104500000000000), (-346778227517372565257136994879948651147709369/108230847523315100656281143583000000000000000)]
    bernstein := [(32410366648399588149041757884174407745520919802551/173169356037304161050049829732800000000000000000000000), (725054669085573599547997801041229843352791098343/2886155933955069350834163828880000000000000000000000), (392029245169280670955113195876209213181949994473/1298770170279781207875373722996000000000000000000000), (2446216855871773056017105089196338554229675963/7215389834887673377085409572200000000000000000000), (392598932388601468646649931816293783568666831/1082308475233151006562811435830000000000000000000)]
    reserve := (93579971/500000000000) }

theorem tilt_045_013_valid : tilt_045_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_045_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_045_013]
  · intro i; fin_cases i <;> norm_num [tilt_045_013]
  · norm_num [tilt_045_013]
  · norm_num [tilt_045_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_045_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_045_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_045_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_045_013]

def tilt_045_014 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(19/200), (1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7720253/50000000), (7720253/50000000), (10308351/100000000), (1832147/12500000), (1832147/12500000), (3760517/25000000), (1806777/12500000)]
    cone := fun i => (![![0, 0, 0, (98629/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5341387/100000000), (1/100000000), (2131869/50000000), (2263921/50000000), (1/100000000), (5309559/100000000), (75257/10000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-1161855064190804308824967394940712707695967029/34336808450200193649341248849230000000000000000), (317665117730961489577/477494242062500000000), (-56059061768353141281049087285394582345119167029/17168404225100096824670624424615000000000000000), (317665117730961489577/477494242062500000000), (-110956268472515478253273207175848451982542367029/34336808450200193649341248849230000000000000000)]
    bernstein := [(11124240402704895484720850301334706457964232164893691/54938893520320309838945998158768000000000000000000000000), (244702269479988557634606188780066798867089350923363/915648225338671830649099969312800000000000000000000000), (131219438115623987433078901670949889658470685992693/412041701402402323792094986190760000000000000000000000), (815193381039836806144621860014658318328563137783/2289120563346679576622749923282000000000000000000000), (130545046272181432972043493483258976590317137171/343368084502001936493412488492300000000000000000000)]
    reserve := (202483881/1000000000000) }

theorem tilt_045_014_valid : tilt_045_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_045_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_045_014]
  · intro i; fin_cases i <;> norm_num [tilt_045_014]
  · norm_num [tilt_045_014]
  · norm_num [tilt_045_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_045_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_045_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_045_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_045_014]

def tilt_045_015 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(19/200), (1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7720253/50000000), (7720253/50000000), (10308351/100000000), (1832147/12500000), (1832147/12500000), (3760517/25000000), (1806777/12500000)]
    cone := fun i => (![![0, 0, 0, (98629/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(14657/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5341387/100000000), (1/100000000), (2131869/50000000), (2263921/50000000), (1/100000000), (2653453/50000000), (4749/625000)]
    alternative := (.spike 3 true false)
    polynomial := [(-8269430355689139087649833094955208427379123/246102182626592151559956464175000000000000000), (370955082748327701431/562458104500000000000), (-398403922490225509669951736242161957220379123/123051091313296075779978232087500000000000000), (370955082748327701431/562458104500000000000), (-788538414624761880252253639389368706013379123/246102182626592151559956464175000000000000000)]
    bernstein := [(54096401398397901950733572882064784740972817071517/393763492202547442495930342680000000000000000000000000), (1321849108705190473677661861877751743135794394781/6562724870042457374932172378000000000000000000000000), (744278751948608897567293644278789037985536203491/2953226191519105818719477570100000000000000000000000), (4744508162748814740209152363587955759259247321/16406812175106143437330430945000000000000000000000), (769977363858951774851679582477304792146066277/2461021826265921515599564641750000000000000000000)]
    reserve := (68691489/500000000000) }

theorem tilt_045_015_valid : tilt_045_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_045_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_045_015]
  · intro i; fin_cases i <;> norm_num [tilt_045_015]
  · norm_num [tilt_045_015]
  · norm_num [tilt_045_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_045_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_045_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_045_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_045_015]

def tilt_045_016 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(19/200), (1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7720253/50000000), (7720253/50000000), (10308351/100000000), (1832147/12500000), (1832147/12500000), (3760517/25000000), (1806777/12500000)]
    cone := fun i => (![![0, 0, 0, (98629/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2171/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5341387/100000000), (1/100000000), (2131869/50000000), (2263921/50000000), (3811/100000000), (2653453/50000000), (75257/10000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-755925758259356557080664781285598189405188925001/22294123648663650344551632928824037500000000000000), (317665117730961489577/477494242062500000000), (-36399457276451654892760994392324275493984967925001/11147061824331825172275816464412018750000000000000), (317665117730961489577/477494242062500000000), (-72042988794643953228441324003362952798564746925001/22294123648663650344551632928824037500000000000000)]
    bernstein := [(4682789593953007268187447687609785597674870788078064679/35670597837861840551282612686118460000000000000000000000000), (116527604321080717709799320589664026791084409638812047/594509963964364009188043544768641000000000000000000000000), (66130271959221440933556968810521514661349225396495817/267529483783963804134619595145888450000000000000000000000), (423304265397191598806763950527758420648413863407027/1486274909910910022970108861921602500000000000000000000), (68854720692942569230093281342707338265005872064799/222941236486636503445516329288240375000000000000000000)]
    reserve := (16409837/125000000000) }

theorem tilt_045_016_valid : tilt_045_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_045_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_045_016]
  · intro i; fin_cases i <;> norm_num [tilt_045_016]
  · norm_num [tilt_045_016]
  · norm_num [tilt_045_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_045_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_045_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_045_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_045_016]

def tilt_045_017 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(19/200), (1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7720253/50000000), (7720253/50000000), (10308351/100000000), (1832147/12500000), (1832147/12500000), (3760517/25000000), (1806777/12500000)]
    cone := fun i => (![![0, 0, 0, (98629/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5341387/100000000), (1/100000000), (2131869/50000000), (2263921/50000000), (1/100000000), (2652127/50000000), (4749/625000)]
    alternative := (.spike 4 false false)
    polynomial := [(-3631440200062013201554577786718369210166109/108230847523315100656281143583000000000000000), (370955082748327701431/562458104500000000000), (-175204834150272654956831412829494886052446109/54115423761657550328140571791500000000000000), (370955082748327701431/562458104500000000000), (-346778228100483296712108247872271402894726109/108230847523315100656281143583000000000000000)]
    bernstein := [(32409416754999762141523875088278048734470500029011/173169356037304161050049829732800000000000000000000000), (725038830076181292542236419468963308469192265123/2886155933955069350834163828880000000000000000000000), (392022114201436444255400613463683035344532471053/1298770170279781207875373722996000000000000000000000), (2446177220086023867256125442041934054260807943/7215389834887673377085409572200000000000000000000), (392592984076029896484898157131903212250902091/1082308475233151006562811435830000000000000000000)]
    reserve := (23394307/125000000000) }

theorem tilt_045_017_valid : tilt_045_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_045_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_045_017]
  · intro i; fin_cases i <;> norm_num [tilt_045_017]
  · norm_num [tilt_045_017]
  · norm_num [tilt_045_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_045_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_045_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_045_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_045_017]

def tilt_045_018 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(19/200), (1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7720253/50000000), (7720253/50000000), (10308351/100000000), (1832147/12500000), (1832147/12500000), (3760517/25000000), (1806777/12500000)]
    cone := fun i => (![![0, 0, 0, (98629/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5341387/100000000), (1/100000000), (2131869/50000000), (2263921/50000000), (1/100000000), (5309559/100000000), (75257/10000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-1161723089372149736444590928888799123406223429/34336808450200193649341248849230000000000000000), (317665117730961489577/477494242062500000000), (-56058929793534486708668710819342668760829423429/17168404225100096824670624424615000000000000000), (317665117730961489577/477494242062500000000), (-110956136497696823680892830709796538398252623429/34336808450200193649341248849230000000000000000)]
    bernstein := [(11339228744405297226195651365408057066060011008589291/54938893520320309838945998158768000000000000000000000000), (248287095276286230437870258454291048990933139774163/915648225338671830649099969312800000000000000000000000), (132833382324342566859448313913088612123670193471493/412041701402402323792094986190760000000000000000000000), (824164105388244054555951386961380383255304860583/2289120563346679576622749923282000000000000000000000), (131891321397276725824263823678829449929991600771/343368084502001936493412488492300000000000000000000)]
    reserve := (51599277/250000000000) }

theorem tilt_045_018_valid : tilt_045_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_045_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_045_018]
  · intro i; fin_cases i <;> norm_num [tilt_045_018]
  · norm_num [tilt_045_018]
  · norm_num [tilt_045_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_045_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_045_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_045_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_045_018]

def tilt_045_019 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(19/200), (1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7720253/50000000), (7720253/50000000), (10308351/100000000), (1832147/12500000), (1832147/12500000), (3760517/25000000), (1806777/12500000)]
    cone := fun i => (![![0, 0, 0, (98629/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5341387/100000000), (1/100000000), (2131869/50000000), (2263921/50000000), (1/100000000), (2653453/50000000), (151241/20000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-1581133599622699351375296225665749125641465257/47025571955310705741098389890450000000000000000), (47070689250737/71062300000000), (-76452088201792651076167090972667060826333050857/23512785977655352870549194945225000000000000000), (47070689250737/71062300000000), (-151323042803962602800958885719668372527024636457/47025571955310705741098389890450000000000000000)]
    bernstein := [(19921593599001298029414082353853007665061602402127303/75240915128497129185757423824720000000000000000000000000), (412749801729363680189617539971586857130549112822479/1254015252141618819762623730412000000000000000000000000), (214451828159110521107942701801016544751162834235369/564306863463728468893180678685400000000000000000000000), (1308585119505057460742620953511148267567777388339/3135038130354047049406559326030000000000000000000000), (207505727738751753740179852354369476646712622143/470255719553107057410983898904500000000000000000000)]
    reserve := (1059083/4000000000) }

theorem tilt_045_019_valid : tilt_045_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_045_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_045_019]
  · intro i; fin_cases i <;> norm_num [tilt_045_019]
  · norm_num [tilt_045_019]
  · norm_num [tilt_045_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_045_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_045_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_045_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_045_019]

def tilt_045_020 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(19/200), (1/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7720253/50000000), (7720253/50000000), (10308351/100000000), (1832147/12500000), (1832147/12500000), (3760517/25000000), (1806777/12500000)]
    cone := fun i => (![![0, 0, 0, (98629/20000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5341387/100000000), (1/100000000), (2131869/50000000), (2263921/50000000), (1/100000000), (2653453/50000000), (151241/20000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-1587654336603104651164325826006098123879465257/47025571955310705741098389890450000000000000000), (47070689250737/71062300000000), (-76445014583281744310198235048912834211827050857/23512785977655352870549194945225000000000000000), (47070689250737/71062300000000), (-151302374829960383969232144271819570299774636457/47025571955310705741098389890450000000000000000)]
    bernstein := [(9695394003987748928516741559541778866252329652127303/75240915128497129185757423824720000000000000000000000000), (242405103674170701193047597093799829842082362822479/1254015252141618819762623730412000000000000000000000000), (137838860192429159951843594913187909476093184235369/564306863463728468893180678685400000000000000000000000), (883195922044230323167762994204752064664827388339/3135038130354047049406559326030000000000000000000000), (143733749610882327875381775149573619395162622143/470255719553107057410983898904500000000000000000000)]
    reserve := (64429001/500000000000) }

theorem tilt_045_020_valid : tilt_045_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_045_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_045_020]
  · intro i; fin_cases i <;> norm_num [tilt_045_020]
  · norm_num [tilt_045_020]
  · norm_num [tilt_045_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_045_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_045_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_045_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_045_020]

def tiltBundle045_row : Alternative → Row
  | .zero => tilt_045_000
  | (.spike 0 false false) => tilt_045_001
  | (.spike 0 false true) => tilt_045_002
  | (.spike 0 true false) => tilt_045_003
  | (.spike 0 true true) => tilt_045_004
  | (.spike 1 false false) => tilt_045_005
  | (.spike 1 false true) => tilt_045_006
  | (.spike 1 true false) => tilt_045_007
  | (.spike 1 true true) => tilt_045_008
  | (.spike 2 false false) => tilt_045_009
  | (.spike 2 false true) => tilt_045_010
  | (.spike 2 true false) => tilt_045_011
  | (.spike 2 true true) => tilt_045_012
  | (.spike 3 false false) => tilt_045_013
  | (.spike 3 false true) => tilt_045_014
  | (.spike 3 true false) => tilt_045_015
  | (.spike 3 true true) => tilt_045_016
  | (.spike 4 false false) => tilt_045_017
  | (.spike 4 false true) => tilt_045_018
  | (.spike 4 true false) => tilt_045_019
  | (.spike 4 true true) => tilt_045_020

def tiltBundle045 : TiltBundle where
  interval := ⟨(19/200), (1/10)⟩
  lambda := ![(7720253/50000000), (7720253/50000000), (10308351/100000000), (1832147/12500000), (1832147/12500000), (3760517/25000000), (1806777/12500000)]
  row := tiltBundle045_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_045_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_045_001_valid | exact tilt_045_002_valid | exact tilt_045_003_valid | exact tilt_045_004_valid | exact tilt_045_005_valid | exact tilt_045_006_valid | exact tilt_045_007_valid | exact tilt_045_008_valid | exact tilt_045_009_valid | exact tilt_045_010_valid | exact tilt_045_011_valid | exact tilt_045_012_valid | exact tilt_045_013_valid | exact tilt_045_014_valid | exact tilt_045_015_valid | exact tilt_045_016_valid | exact tilt_045_017_valid | exact tilt_045_018_valid | exact tilt_045_019_valid | exact tilt_045_020_valid
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
