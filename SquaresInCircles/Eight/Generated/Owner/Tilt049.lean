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

def tilt_049_000 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11141201/50000000), (11141201/50000000), (15304161/100000000), (10032759/50000000), (10032759/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11141201/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (10032759/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3981269/100000000), (1/100000000), (599469/10000000), (6376619/100000000), (1/100000000), (896293/25000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-18698203227992422695139348578006031345873/341011271506249039717352175000000000000000), (2991346207673/5258500000000), (-94683705610326288846099423967249531345873/170505635753124519858676087500000000000000), (2991346207673/5258500000000), (-170669207992660154997059499356493031345873/341011271506249039717352175000000000000000)]
    bernstein := [(36909006483249645004156347657744432503651/4297791286429526359022383104000000000000000), (7974102155548422298509486471675405988095113/698391084044798033341137254400000000000000000), (17591717858762923322468837939495581850171/1238223519061979398151040000000000000000000), (28468438134022590134477252167231125201129593/1678824721261533733993118400000000000000000000), (1073191537453256495745511464817804104431018687/54561803440999846354776348000000000000000000000)]
    reserve := (2146975273/250000000000) }

theorem tilt_049_000_valid : tilt_049_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_049_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_049_000]
  · intro i; fin_cases i <;> norm_num [tilt_049_000]
  · norm_num [tilt_049_000]
  · norm_num [tilt_049_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_049_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_049_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_049_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_049_000]

def tilt_049_001 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11141201/50000000), (11141201/50000000), (15304161/100000000), (10032759/50000000), (10032759/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11141201/100000000), 0], ![(11141/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (10032759/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3981269/100000000), (1/100000000), (599469/10000000), (6376619/100000000), (1/100000000), (896293/25000000), (1/100000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-18615887223287612217763384334943858567623/341011271506249039717352175000000000000000), (2991346207673/5258500000000), (-94601389605621478368723459724187358567623/170505635753124519858676087500000000000000), (2991346207673/5258500000000), (-170586891987955344519683535113430858567623/341011271506249039717352175000000000000000)]
    bernstein := [(37979114544412181210043882817552678620901/4297791286429526359022383104000000000000000), (8148529769517915700069154702724150105206863/698391084044798033341137254400000000000000000), (17901985876496439737193626240268386937421/1238223519061979398151040000000000000000000), (28890573602149943987955975874325423094021343/1678824721261533733993118400000000000000000000), (1086961441036281897211440139361487428949456937/54561803440999846354776348000000000000000000000)]
    reserve := (8836891327/1000000000000) }

theorem tilt_049_001_valid : tilt_049_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_049_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_049_001]
  · intro i; fin_cases i <;> norm_num [tilt_049_001]
  · norm_num [tilt_049_001]
  · norm_num [tilt_049_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_049_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_049_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_049_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_049_001]

def tilt_049_002 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11141201/50000000), (11141201/50000000), (15304161/100000000), (10032759/50000000), (10032759/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11141201/100000000), 0], ![0, 0, (33/500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (10032759/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3981269/100000000), (5793/100000000), (599469/10000000), (6376619/100000000), (1/100000000), (896293/25000000), (1/100000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-36237522176695203414270888541578921475860541/658492765278566895694207049925000000000000000), (2991346207673/5258500000000), (-182965527276981898951774794118208119975860541/329246382639283447847103524962500000000000000), (2991346207673/5258500000000), (-329693532377268594489278699694837318475860541/658492765278566895694207049925000000000000000)]
    bernstein := [(69564498854411207033587423640263924853812967/8299034974095415399272221773824000000000000000), (15119784058010754690903345535850195350361513621/1348593183290505002381736038246400000000000000000), (33474738306144287681234747950780239906371807/2391009615308682217829658240000000000000000000), (54299259678333250272071695876044009464127331781/3241810536756021640340711630400000000000000000000), (2050370244687544660873418100900227563250572840979/105358842444570703311073127988000000000000000000000)]
    reserve := (8382239509/1000000000000) }

theorem tilt_049_002_valid : tilt_049_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_049_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_049_002]
  · intro i; fin_cases i <;> norm_num [tilt_049_002]
  · norm_num [tilt_049_002]
  · norm_num [tilt_049_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_049_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_049_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_049_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_049_002]

def tilt_049_003 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11141201/50000000), (11141201/50000000), (15304161/100000000), (10032759/50000000), (10032759/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (5576171/50000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (10032759/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(497161/12500000), (1/100000000), (599469/10000000), (6376619/100000000), (1/100000000), (896293/25000000), (1/100000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-9286646755269996561650667417976393000589/170335141637822793521280300000000000000000), (2991346207673/5258500000000), (-47241407762279055461692299410782393000589/85167570818911396760640150000000000000000), (2991346207673/5258500000000), (-85196168769288114361733931403588393000589/170335141637822793521280300000000000000000)]
    bernstein := [(19126433039652713871518715224034730992343/2146746892764683576194351104000000000000000), (4095596733948643939369612236845648391751909/348846370074261081131582054400000000000000000), (2088889936344565396965601466606479362791683/143755372283349346620157440000000000000000000), (14492327626772350853194113521058962186902549/838573004986204521950918400000000000000000000), (544942899038149528340704365748718786468471491/27253622662051646963404848000000000000000000000)]
    reserve := (4454748043/500000000000) }

theorem tilt_049_003_valid : tilt_049_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_049_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_049_003]
  · intro i; fin_cases i <;> norm_num [tilt_049_003]
  · norm_num [tilt_049_003]
  · norm_num [tilt_049_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_049_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_049_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_049_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_049_003]

def tilt_049_004 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11141201/50000000), (11141201/50000000), (15304161/100000000), (10032759/50000000), (10032759/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (556503/5000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (10032759/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3985251/100000000), (1/100000000), (599469/10000000), (6376619/100000000), (1/100000000), (896293/25000000), (1/100000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-130189366601887565316240897999469509761/2370502398546987732817339062500000000000), (2991346207673/5258500000000), (-658394240465769530833286313608750759761/1185251199273493866408669531250000000000), (2991346207673/5258500000000), (-1186599114329651496350331729218032009761/2370502398546987732817339062500000000000)]
    bernstein := [(253827716840092660079459876641648873107/29875624075226036164984064000000000000000), (54984281680861456402397470753107278191441/4854788912224230876809910400000000000000000), (197667666601729932793952038200191663813369/14004198785262204452336280000000000000000000), (196813879015465265563513276790415764106801/11670165654385170376946900000000000000000000), (7424900125607441118105189524658669312670159/379280383767518037250774250000000000000000000)]
    reserve := (8496147769/1000000000000) }

theorem tilt_049_004_valid : tilt_049_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_049_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_049_004]
  · intro i; fin_cases i <;> norm_num [tilt_049_004]
  · norm_num [tilt_049_004]
  · norm_num [tilt_049_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_049_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_049_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_049_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_049_004]

def tilt_049_005 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11141201/50000000), (11141201/50000000), (15304161/100000000), (10032759/50000000), (10032759/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11141201/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (10032759/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3981269/100000000), (1/100000000), (599469/10000000), (1274709/20000000), (1/100000000), (896293/25000000), (1/100000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-2480950416811461288968810044328192673163/45446250527691786422560950000000000000000), (2991346207673/5258500000000), (-12607466653318866460625259618347192673163/22723125263845893211280475000000000000000), (2991346207673/5258500000000), (-22733982889826271632281709192366192673163/45446250527691786422560950000000000000000)]
    bernstein := [(5061067880581737212873419371423655248881/572762591265924791344029696000000000000000), (1085886095246828628900044002264554065567603/93073921080712778593404825600000000000000000), (2385672656066378192025586505733689155001/165016880550646739976960000000000000000000), (3850072396510223521509890820905431612172483/223735387213251871618761600000000000000000000), (144853527753584990231100705670112117440620197/7271400084430685827609752000000000000000000000)]
    reserve := (8836240281/1000000000000) }

theorem tilt_049_005_valid : tilt_049_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_049_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_049_005]
  · intro i; fin_cases i <;> norm_num [tilt_049_005]
  · norm_num [tilt_049_005]
  · norm_num [tilt_049_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_049_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_049_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_049_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_049_005]

def tilt_049_006 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11141201/50000000), (11141201/50000000), (15304161/100000000), (10032759/50000000), (10032759/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11141201/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (10032759/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3981269/100000000), (1/100000000), (599469/10000000), (1275939/20000000), (1/100000000), (896293/25000000), (1/100000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-92529246086592898617429849319414611099/1684818622279383569874350000000000000000), (2991346207673/5258500000000), (-467947304473746708778783411206414611099/842409311139691784937175000000000000000), (2991346207673/5258500000000), (-843365362860900518940136973093414611099/1684818622279383569874350000000000000000)]
    bernstein := [(180431948860241342570513658669290055713/21233898698019554160631808000000000000000), (39083882139850437524671503173057259081219/3450508538428177551102668800000000000000000), (12336732238592066096911122567745978639/873947670093657565440000000000000000000), (139894241369185597243247869238797293989459/8294491678913888343996800000000000000000000), (5277527297482108766067783876578672440748181/269570979564701371179896000000000000000000000)]
    reserve := (2124338439/250000000000) }

theorem tilt_049_006_valid : tilt_049_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_049_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_049_006]
  · intro i; fin_cases i <;> norm_num [tilt_049_006]
  · norm_num [tilt_049_006]
  · norm_num [tilt_049_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_049_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_049_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_049_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_049_006]

def tilt_049_007 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11141201/50000000), (11141201/50000000), (15304161/100000000), (10032759/50000000), (10032759/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11141201/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (10032759/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3981269/100000000), (1/100000000), (599117/10000000), (6376619/100000000), (1/100000000), (896293/25000000), (1/100000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-74417241535871931036531844754323899770671/1363244137401663178101559100000000000000000), (170506733837361/299558500000000), (-378568755284892980925223901570565300070671/681622068700831589050779550000000000000000), (170506733837361/299558500000000), (-682720269033914030813915958386806700370671/1363244137401663178101559100000000000000000)]
    bernstein := [(1981650477747137893475218826105858137196601/223353919471888495100159442944000000000000000), (32677243866015354185232699722904856164468151/2791923993398606188751993036800000000000000000), (310930820957047242011225112560291018745707/21449938486467472255316480000000000000000000), (1504832595531651069090377796390753074980476443/87247624793706443398499782400000000000000000000), (4354049735112710051855305192614141257453784449/218119061984266108496249456000000000000000000000)]
    reserve := (4436122013/500000000000) }

theorem tilt_049_007_valid : tilt_049_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_049_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_049_007]
  · intro i; fin_cases i <;> norm_num [tilt_049_007]
  · norm_num [tilt_049_007]
  · norm_num [tilt_049_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_049_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_049_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_049_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_049_007]

def tilt_049_008 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11141201/50000000), (11141201/50000000), (15304161/100000000), (10032759/50000000), (10032759/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11141201/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (10032759/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3981269/100000000), (1/100000000), (599821/10000000), (6376619/100000000), (1/100000000), (896293/25000000), (1/100000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-74959993309571801878480184783999956334383/1364846034648329139637258300000000000000000), (170506733837361/299910500000000), (-378692498619221681197468731081706556034383/682423017324164569818629150000000000000000), (170506733837361/299910500000000), (-682425003928871560516457277379413155734383/1364846034648329139637258300000000000000000)]
    bernstein := [(1892104271876589808148407615786985541049273/223616374316782246238168399872000000000000000), (31557153861804303683934938553148384028922423/2795204678959778077977104998400000000000000000), (906957352386489083162119003227162794615233/64425430523043440641758720000000000000000000), (1469777771770067713184989068969272164863888539/87350146217493064936784531200000000000000000000), (4266342415787072515277502168547354041436677377/218375365543732662341961328000000000000000000000)]
    reserve := (8461385163/1000000000000) }

theorem tilt_049_008_valid : tilt_049_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_049_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_049_008]
  · intro i; fin_cases i <;> norm_num [tilt_049_008]
  · norm_num [tilt_049_008]
  · norm_num [tilt_049_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_049_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_049_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_049_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_049_008]

def tilt_049_009 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11141201/50000000), (11141201/50000000), (15304161/100000000), (10032759/50000000), (10032759/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11141201/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (10032759/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3981269/100000000), (1/100000000), (599469/10000000), (3186773/50000000), (1/100000000), (896293/25000000), (1/100000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-18607153560945662125141280397424736150459/340846932436071143986236450000000000000000), (2991346207673/5258500000000), (-94556037251019427434153310856953736150459/170423466218035571993118225000000000000000), (2991346207673/5258500000000), (-170504920941093192743165341316482736150459/340846932436071143986236450000000000000000)]
    bernstein := [(37957722359353348229166459680114990044033/4295720108486607402361921536000000000000000), (8144099281963575801465868279532537037177379/698054517629073702883812249600000000000000000), (17892462861967565692930118914187179125193/1237626798311676226095360000000000000000000), (28875432040046019831908812139324045996719219/1678015667377581016547625600000000000000000000), (1086397862203363369451531333049838868015068021/54535509189771383037797832000000000000000000000)]
    reserve := (8836172143/1000000000000) }

theorem tilt_049_009_valid : tilt_049_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_049_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_049_009]
  · intro i; fin_cases i <;> norm_num [tilt_049_009]
  · norm_num [tilt_049_009]
  · norm_num [tilt_049_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_049_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_049_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_049_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_049_009]

def tilt_049_010 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11141201/50000000), (11141201/50000000), (15304161/100000000), (10032759/50000000), (10032759/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11141201/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (10032759/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3981269/100000000), (1/100000000), (599469/10000000), (398731/6250000), (1/100000000), (896293/25000000), (1/100000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-9360476592982223800420432523586939005917/170587912244978959358292600000000000000000), (2991346207673/5258500000000), (-47371560962815660340051809991838939005917/85293956122489479679146300000000000000000), (2991346207673/5258500000000), (-85382645332649096879683187460090939005917/170587912244978959358292600000000000000000)]
    bernstein := [(18374181228891654877487664419795072923079/2149932580170565592404819968000000000000000), (3974430984491458020004944460562876966461877/349364044277716908765783244800000000000000000), (8774232732917203954329112055235014516159/619410508269792637639680000000000000000000), (14205889452901826196935315647575384807117797/839817414129127184533132800000000000000000000), (535706545808923898497537969703605784151198323/27294065959196633497326816000000000000000000000)]
    reserve := (4273199401/500000000000) }

theorem tilt_049_010_valid : tilt_049_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_049_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_049_010]
  · intro i; fin_cases i <;> norm_num [tilt_049_010]
  · norm_num [tilt_049_010]
  · norm_num [tilt_049_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_049_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_049_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_049_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_049_010]

def tilt_049_011 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11141201/50000000), (11141201/50000000), (15304161/100000000), (10032759/50000000), (10032759/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11141201/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(10033/50000000), 0, 0, 0, 0], ![0, 0, 0, (10032759/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3981269/100000000), (1/100000000), (599469/10000000), (6376619/100000000), (1/100000000), (896293/25000000), (1/100000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-6208024609167677235116120819395407702541/113670423835416346572450725000000000000000), (2991346207673/5258500000000), (-31536525403278965952102812615809907702541/56835211917708173286225362500000000000000), (2991346207673/5258500000000), (-56865026197390254669089504412224407702541/113670423835416346572450725000000000000000)]
    bernstein := [(12624229563203909290479722405133979866967/1432597095476508786340794368000000000000000), (2710394118395147268625528686524526548315621/232797028014932677780379084800000000000000000), (1985680963999129587109856522090710835269/137580391006886599794560000000000000000000), (9616196935505638483707691021129020088053781/559608240420511244664372800000000000000000000), (361863992565507436636245804642460482111238979/18187267813666615451592116000000000000000000000)]
    reserve := (1101516051/125000000000) }

theorem tilt_049_011_valid : tilt_049_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_049_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_049_011]
  · intro i; fin_cases i <;> norm_num [tilt_049_011]
  · norm_num [tilt_049_011]
  · norm_num [tilt_049_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_049_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_049_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_049_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_049_011]

def tilt_049_012 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11141201/50000000), (11141201/50000000), (15304161/100000000), (10032759/50000000), (10032759/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11141201/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (743/12500000), 0, 0], ![0, 0, 0, (10032759/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3981269/100000000), (1/100000000), (599469/10000000), (6376619/100000000), (5217/100000000), (896293/25000000), (1/100000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-10874215663002922895496421595785431951706111/197672867049789026689491810775000000000000000), (2991346207673/5258500000000), (-54920478543962453974336278629750247451706111/98836433524894513344745905387500000000000000), (2991346207673/5258500000000), (-98966741424921985053176135663715062951706111/197672867049789026689491810775000000000000000)]
    bernstein := [(20933543930827279868960899881389357547820557/2491286349033648779446641405952000000000000000), (4547116793316917203028910392740554416664750791/404834031717967926660079228467200000000000000000), (10063560472617591594579437856363847666646197/717756899882927391128219520000000000000000000), (16320201035128046424242517566285559568627592151/973158730091269054471344299200000000000000000000), (616156470668329404300707157315219413728650045809/31627658727966244270318689724000000000000000000000)]
    reserve := (8402704867/1000000000000) }

theorem tilt_049_012_valid : tilt_049_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_049_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_049_012]
  · intro i; fin_cases i <;> norm_num [tilt_049_012]
  · norm_num [tilt_049_012]
  · norm_num [tilt_049_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_049_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_049_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_049_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_049_012]

def tilt_049_013 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11141201/50000000), (11141201/50000000), (15304161/100000000), (10032759/50000000), (10032759/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11141201/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (1255349/12500000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3981269/100000000), (1/100000000), (599469/10000000), (6376619/100000000), (1/100000000), (1790793/50000000), (1/100000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-12389236735943127182386398861263972688623/227113454318506052738913225000000000000000), (2991346207673/5258500000000), (-62995569623279006248003054086928472688623/113556727159253026369456612500000000000000), (2991346207673/5258500000000), (-113601902510614885313619709312592972688623/227113454318506052738913225000000000000000)]
    bernstein := [(25410321189849328717194615324062635047901/2862328335041848590826426368000000000000000), (5445866162273840082884183347437692342807863/465128354444300396009294284800000000000000000), (11956421617246149931807972254117541404421/824656673049088215703680000000000000000000), (19286970561750910592866650199687774170582343/1118097005875722105791572800000000000000000000), (725411860059110968467749691610092062674455937/36338152690960968438226116000000000000000000000)]
    reserve := (8877500487/1000000000000) }

theorem tilt_049_013_valid : tilt_049_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_049_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_049_013]
  · intro i; fin_cases i <;> norm_num [tilt_049_013]
  · norm_num [tilt_049_013]
  · norm_num [tilt_049_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_049_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_049_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_049_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_049_013]

def tilt_049_014 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11141201/50000000), (11141201/50000000), (15304161/100000000), (10032759/50000000), (10032759/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11141201/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (5011363/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3981269/100000000), (1/100000000), (599469/10000000), (6376619/100000000), (1/100000000), (3588757/100000000), (1/100000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-149953948291417222089286558982342526929849/2730818131340871311120193150000000000000000), (2991346207673/5258500000000), (-758445822205678157935758699841805526929849/1365409065670435655560096575000000000000000), (2991346207673/5258500000000), (-1366937696119939093782230840701268526929849/2730818131340871311120193150000000000000000)]
    bernstein := [(292723637517012580333729700864089469911963/34416710972222181201071726592000000000000000), (63393088426832014734415739653175349615649969/5592715532986104445174155571200000000000000000), (140049973177679933710162321128531536956723/9915693465414349992625920000000000000000000), (226853471846867880483435947263969277959058209/13444027723524289531668643200000000000000000000), (8557525701942769323594636876134991484647929431/436930901014539409779230904000000000000000000000)]
    reserve := (8505276339/1000000000000) }

theorem tilt_049_014_valid : tilt_049_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_049_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_049_014]
  · intro i; fin_cases i <;> norm_num [tilt_049_014]
  · norm_num [tilt_049_014]
  · norm_num [tilt_049_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_049_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_049_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_049_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_049_014]

def tilt_049_015 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11141201/50000000), (11141201/50000000), (15304161/100000000), (10032759/50000000), (10032759/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11141201/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(10033/50000000), 0, 0, 0, 0], ![0, 0, 0, (10032759/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3981269/100000000), (1/100000000), (599469/10000000), (6376619/100000000), (1/100000000), (896293/25000000), (1/100000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-6208024609167677235116120819395407702541/113670423835416346572450725000000000000000), (2991346207673/5258500000000), (-31536525403278965952102812615809907702541/56835211917708173286225362500000000000000), (2991346207673/5258500000000), (-56865026197390254669089504412224407702541/113670423835416346572450725000000000000000)]
    bernstein := [(12624229563203909290479722405133979866967/1432597095476508786340794368000000000000000), (2710394118395147268625528686524526548315621/232797028014932677780379084800000000000000000), (1985680963999129587109856522090710835269/137580391006886599794560000000000000000000), (9616196935505638483707691021129020088053781/559608240420511244664372800000000000000000000), (361863992565507436636245804642460482111238979/18187267813666615451592116000000000000000000000)]
    reserve := (1101516051/125000000000) }

theorem tilt_049_015_valid : tilt_049_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_049_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_049_015]
  · intro i; fin_cases i <;> norm_num [tilt_049_015]
  · norm_num [tilt_049_015]
  · norm_num [tilt_049_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_049_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_049_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_049_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_049_015]

def tilt_049_016 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11141201/50000000), (11141201/50000000), (15304161/100000000), (10032759/50000000), (10032759/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11141201/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (743/12500000), 0, 0], ![0, 0, 0, (10032759/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3981269/100000000), (1/100000000), (599469/10000000), (6376619/100000000), (5217/100000000), (896293/25000000), (1/100000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-10874215663002922895496421595785431951706111/197672867049789026689491810775000000000000000), (2991346207673/5258500000000), (-54920478543962453974336278629750247451706111/98836433524894513344745905387500000000000000), (2991346207673/5258500000000), (-98966741424921985053176135663715062951706111/197672867049789026689491810775000000000000000)]
    bernstein := [(20933543930827279868960899881389357547820557/2491286349033648779446641405952000000000000000), (4547116793316917203028910392740554416664750791/404834031717967926660079228467200000000000000000), (10063560472617591594579437856363847666646197/717756899882927391128219520000000000000000000), (16320201035128046424242517566285559568627592151/973158730091269054471344299200000000000000000000), (616156470668329404300707157315219413728650045809/31627658727966244270318689724000000000000000000000)]
    reserve := (8402704867/1000000000000) }

theorem tilt_049_016_valid : tilt_049_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_049_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_049_016]
  · intro i; fin_cases i <;> norm_num [tilt_049_016]
  · norm_num [tilt_049_016]
  · norm_num [tilt_049_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_049_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_049_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_049_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_049_016]

def tilt_049_017 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11141201/50000000), (11141201/50000000), (15304161/100000000), (10032759/50000000), (10032759/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11141201/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (10032759/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3981269/100000000), (1/100000000), (599469/10000000), (6376619/100000000), (1/100000000), (896293/25000000), (1/100000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-18698203227992422695139348578006031345873/341011271506249039717352175000000000000000), (2991346207673/5258500000000), (-94683705610326288846099423967249531345873/170505635753124519858676087500000000000000), (2991346207673/5258500000000), (-170669207992660154997059499356493031345873/341011271506249039717352175000000000000000)]
    bernstein := [(36909006483249645004156347657744432503651/4297791286429526359022383104000000000000000), (7974102155548422298509486471675405988095113/698391084044798033341137254400000000000000000), (17591717858762923322468837939495581850171/1238223519061979398151040000000000000000000), (28468438134022590134477252167231125201129593/1678824721261533733993118400000000000000000000), (1073191537453256495745511464817804104431018687/54561803440999846354776348000000000000000000000)]
    reserve := (2146975273/250000000000) }

theorem tilt_049_017_valid : tilt_049_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_049_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_049_017]
  · intro i; fin_cases i <;> norm_num [tilt_049_017]
  · norm_num [tilt_049_017]
  · norm_num [tilt_049_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_049_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_049_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_049_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_049_017]

def tilt_049_018 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11141201/50000000), (11141201/50000000), (15304161/100000000), (10032759/50000000), (10032759/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11141201/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (10032759/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3981269/100000000), (1/100000000), (599469/10000000), (6376619/100000000), (1/100000000), (896293/25000000), (1/100000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-18698203227992422695139348578006031345873/341011271506249039717352175000000000000000), (2991346207673/5258500000000), (-94683705610326288846099423967249531345873/170505635753124519858676087500000000000000), (2991346207673/5258500000000), (-170669207992660154997059499356493031345873/341011271506249039717352175000000000000000)]
    bernstein := [(36909006483249645004156347657744432503651/4297791286429526359022383104000000000000000), (7974102155548422298509486471675405988095113/698391084044798033341137254400000000000000000), (17591717858762923322468837939495581850171/1238223519061979398151040000000000000000000), (28468438134022590134477252167231125201129593/1678824721261533733993118400000000000000000000), (1073191537453256495745511464817804104431018687/54561803440999846354776348000000000000000000000)]
    reserve := (2146975273/250000000000) }

theorem tilt_049_018_valid : tilt_049_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_049_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_049_018]
  · intro i; fin_cases i <;> norm_num [tilt_049_018]
  · norm_num [tilt_049_018]
  · norm_num [tilt_049_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_049_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_049_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_049_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_049_018]

def tilt_049_019 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11141201/50000000), (11141201/50000000), (15304161/100000000), (10032759/50000000), (10032759/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11141201/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (10032759/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3981269/100000000), (1/100000000), (599469/10000000), (6376619/100000000), (1/100000000), (896293/25000000), (1/100000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-18698203227992422695139348578006031345873/341011271506249039717352175000000000000000), (2991346207673/5258500000000), (-94683705610326288846099423967249531345873/170505635753124519858676087500000000000000), (2991346207673/5258500000000), (-170669207992660154997059499356493031345873/341011271506249039717352175000000000000000)]
    bernstein := [(36909006483249645004156347657744432503651/4297791286429526359022383104000000000000000), (7974102155548422298509486471675405988095113/698391084044798033341137254400000000000000000), (17591717858762923322468837939495581850171/1238223519061979398151040000000000000000000), (28468438134022590134477252167231125201129593/1678824721261533733993118400000000000000000000), (1073191537453256495745511464817804104431018687/54561803440999846354776348000000000000000000000)]
    reserve := (2146975273/250000000000) }

theorem tilt_049_019_valid : tilt_049_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_049_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_049_019]
  · intro i; fin_cases i <;> norm_num [tilt_049_019]
  · norm_num [tilt_049_019]
  · norm_num [tilt_049_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_049_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_049_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_049_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_049_019]

def tilt_049_020 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11141201/50000000), (11141201/50000000), (15304161/100000000), (10032759/50000000), (10032759/50000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11141201/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (10032759/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3981269/100000000), (1/100000000), (599469/10000000), (6376619/100000000), (1/100000000), (896293/25000000), (1/100000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-18698203227992422695139348578006031345873/341011271506249039717352175000000000000000), (2991346207673/5258500000000), (-94683705610326288846099423967249531345873/170505635753124519858676087500000000000000), (2991346207673/5258500000000), (-170669207992660154997059499356493031345873/341011271506249039717352175000000000000000)]
    bernstein := [(36909006483249645004156347657744432503651/4297791286429526359022383104000000000000000), (7974102155548422298509486471675405988095113/698391084044798033341137254400000000000000000), (17591717858762923322468837939495581850171/1238223519061979398151040000000000000000000), (28468438134022590134477252167231125201129593/1678824721261533733993118400000000000000000000), (1073191537453256495745511464817804104431018687/54561803440999846354776348000000000000000000000)]
    reserve := (2146975273/250000000000) }

theorem tilt_049_020_valid : tilt_049_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_049_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_049_020]
  · intro i; fin_cases i <;> norm_num [tilt_049_020]
  · norm_num [tilt_049_020]
  · norm_num [tilt_049_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_049_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_049_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_049_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_049_020]

def tiltBundle049_row : Alternative → Row
  | .zero => tilt_049_000
  | (.spike 0 false false) => tilt_049_001
  | (.spike 0 false true) => tilt_049_002
  | (.spike 0 true false) => tilt_049_003
  | (.spike 0 true true) => tilt_049_004
  | (.spike 1 false false) => tilt_049_005
  | (.spike 1 false true) => tilt_049_006
  | (.spike 1 true false) => tilt_049_007
  | (.spike 1 true true) => tilt_049_008
  | (.spike 2 false false) => tilt_049_009
  | (.spike 2 false true) => tilt_049_010
  | (.spike 2 true false) => tilt_049_011
  | (.spike 2 true true) => tilt_049_012
  | (.spike 3 false false) => tilt_049_013
  | (.spike 3 false true) => tilt_049_014
  | (.spike 3 true false) => tilt_049_015
  | (.spike 3 true true) => tilt_049_016
  | (.spike 4 false false) => tilt_049_017
  | (.spike 4 false true) => tilt_049_018
  | (.spike 4 true false) => tilt_049_019
  | (.spike 4 true true) => tilt_049_020

def tiltBundle049 : TiltBundle where
  interval := ⟨(1/8), (3/20)⟩
  lambda := ![(11141201/50000000), (11141201/50000000), (15304161/100000000), (10032759/50000000), (10032759/50000000), 0, 0]
  row := tiltBundle049_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_049_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_049_001_valid | exact tilt_049_002_valid | exact tilt_049_003_valid | exact tilt_049_004_valid | exact tilt_049_005_valid | exact tilt_049_006_valid | exact tilt_049_007_valid | exact tilt_049_008_valid | exact tilt_049_009_valid | exact tilt_049_010_valid | exact tilt_049_011_valid | exact tilt_049_012_valid | exact tilt_049_013_valid | exact tilt_049_014_valid | exact tilt_049_015_valid | exact tilt_049_016_valid | exact tilt_049_017_valid | exact tilt_049_018_valid | exact tilt_049_019_valid | exact tilt_049_020_valid
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
