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

def tilt_054_000 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11141347/50000000), (11141347/50000000), (17226061/100000000), (4776069/25000000), (4776069/25000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11141347/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4776069/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1990661/50000000), (1/100000000), (656481/12500000), (812491/12500000), (1/100000000), (3413423/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-15442738570603636320503517568441163925839/181216668912440430019855650000000000000000), (27417360434881/37513200000000), (-55822694381355865274112091299652163925839/90608334456220215009927825000000000000000), (27417360434881/37513200000000), (-96202650192108094227720665030863163925839/181216668912440430019855650000000000000000)]
    bernstein := [(3170475169513835747029730836167953125432529/46391467241584750085083046400000000000000000), (11077288238897662560235190429038979030862009/154638224138615833616943488000000000000000000), (1042382238596807918232352947884299907060811979/13917440172475425025524913920000000000000000000), (1208258128025167583439454118123810992991971617/15463822413861583361694348800000000000000000000), (12579046204213975836898217888040174666576363467/154638224138615833616943488000000000000000000000)]
    reserve := (34170886997/500000000000) }

theorem tilt_054_000_valid : tilt_054_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_054_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_054_000]
  · intro i; fin_cases i <;> norm_num [tilt_054_000]
  · norm_num [tilt_054_000]
  · norm_num [tilt_054_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_054_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_054_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_054_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_054_000]

def tilt_054_001 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11141347/50000000), (11141347/50000000), (17226061/100000000), (4776069/25000000), (4776069/25000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11141347/100000000), 0], ![(22283/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4776069/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1990661/50000000), (1/100000000), (656481/12500000), (812491/12500000), (1/100000000), (3413423/100000000), (1/100000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-15398993060163073986776929694425548034339/181216668912440430019855650000000000000000), (27417360434881/37513200000000), (-55778948870915302940385503425636548034339/90608334456220215009927825000000000000000), (27417360434881/37513200000000), (-96158904681667531893994077156847548034339/181216668912440430019855650000000000000000)]
    bernstein := [(1061039207343719420492238243919488706025343/15463822413861583361694348800000000000000000), (11119677638514567461616254078960110829725509/154638224138615833616943488000000000000000000), (1046220425937352416831190041362556029765130479/13917440172475425025524913920000000000000000000), (1212549431362855426691031208801120865100447117/15463822413861583361694348800000000000000000000), (37866705859030713093781744419482809787425341901/463914672415847500850830464000000000000000000000)]
    reserve := (34307145379/500000000000) }

theorem tilt_054_001_valid : tilt_054_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_054_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_054_001]
  · intro i; fin_cases i <;> norm_num [tilt_054_001]
  · norm_num [tilt_054_001]
  · norm_num [tilt_054_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_054_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_054_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_054_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_054_001]

def tilt_054_002 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11141347/50000000), (11141347/50000000), (17226061/100000000), (4776069/25000000), (4776069/25000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11141347/100000000), 0], ![0, 0, (33/500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4776069/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1990661/50000000), (5793/100000000), (656481/12500000), (812491/12500000), (1/100000000), (3413423/100000000), (1/100000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-9963232929692197142767019246472181484195051/116643129223307490122780420050000000000000000), (27417360434881/37513200000000), (-35954464486546381845906404538128328484195051/58321564611653745061390210025000000000000000), (27417360434881/37513200000000), (-61945696043400566549045789829784475484195051/116643129223307490122780420050000000000000000)]
    bernstein := [(6102023846260576586119277068675643637702890783/89581923243500152414295362598400000000000000000), (21322635868956886770901059128475067961069986743/298606410811667174714317875328000000000000000000), (668906166415414216725560627471049599916960420311/8958192324350015241429536259840000000000000000000), (2326302157761887199607266251015395254391629246159/29860641081166717471431787532800000000000000000000), (72663765209966679105455865356792560379203737853327/895819232435001524142953625984000000000000000000000)]
    reserve := (68116687221/1000000000000) }

theorem tilt_054_002_valid : tilt_054_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_054_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_054_002]
  · intro i; fin_cases i <;> norm_num [tilt_054_002]
  · norm_num [tilt_054_002]
  · norm_num [tilt_054_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_054_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_054_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_054_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_054_002]

def tilt_054_003 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11141347/50000000), (11141347/50000000), (17226061/100000000), (4776069/25000000), (4776069/25000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (1394061/12500000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4776069/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(198867/5000000), (1/100000000), (656481/12500000), (812491/12500000), (1/100000000), (3413423/100000000), (1/100000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-25618083307695496993339422426334336027/301725702305333848043092500000000000000), (27417360434881/37513200000000), (-92850698271743984031206712338284336027/150862851152666924021546250000000000000), (27417360434881/37513200000000), (-160083313235792471069074002250234336027/301725702305333848043092500000000000000)]
    bernstein := [(1768675691284226215501376832681050629399/25747259930055155033010560000000000000000), (18534837570160109450316795690103997139837/257472599300551550330105600000000000000000), (1743819917189656795874859902293045378827047/23172533937049639529709504000000000000000000), (2020977624087787211939224906230999045009381/25747259930055155033010560000000000000000000), (63110951472684397404024182515925006197454293/772417797901654650990316800000000000000000000)]
    reserve := (68693744347/1000000000000) }

theorem tilt_054_003_valid : tilt_054_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_054_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_054_003]
  · intro i; fin_cases i <;> norm_num [tilt_054_003]
  · norm_num [tilt_054_003]
  · norm_num [tilt_054_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_054_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_054_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_054_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_054_003]

def tilt_054_004 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11141347/50000000), (11141347/50000000), (17226061/100000000), (4776069/25000000), (4776069/25000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (5565103/50000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4776069/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3985303/100000000), (1/100000000), (656481/12500000), (812491/12500000), (1/100000000), (3413423/100000000), (1/100000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-157901183161183970432326412373564184873/1850998682907888341445637500000000000000), (27417360434881/37513200000000), (-570353555617579031418332992847814184873/925499341453944170722818750000000000000), (27417360434881/37513200000000), (-982805928073974092404339573322064184873/1850998682907888341445637500000000000000)]
    bernstein := [(32336552205816158681551997720924075571703/473855662824419415410083200000000000000000), (112987030145046230808720929416917711108063/1579518876081398051366944000000000000000000), (10632742752171980968283969151688876045927853/142156698847325824623024960000000000000000000), (12325340878271129454925688780978215875263319/157951887608139805136694400000000000000000000), (128323403944868149949775864944603050453856269/1579518876081398051366944000000000000000000000)]
    reserve := (68241354367/1000000000000) }

theorem tilt_054_004_valid : tilt_054_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_054_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_054_004]
  · intro i; fin_cases i <;> norm_num [tilt_054_004]
  · norm_num [tilt_054_004]
  · norm_num [tilt_054_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_054_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_054_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_054_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_054_004]

def tilt_054_005 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11141347/50000000), (11141347/50000000), (17226061/100000000), (4776069/25000000), (4776069/25000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11141347/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4776069/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1990661/50000000), (1/100000000), (656481/12500000), (812087/12500000), (1/100000000), (3413423/100000000), (1/100000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-24622747127193142837806950678520671393347/289802498257033269771179280000000000000000), (27417360434881/37513200000000), (-89198551018163199819113329832323871393347/144901249128516634885589640000000000000000), (27417360434881/37513200000000), (-153774354909133256800419708986127071393347/289802498257033269771179280000000000000000)]
    bernstein := [(5091435679899077540181578355538040367322717/74189439553800517061421895680000000000000000), (17785923207827729322811869189027348419846757/247298131846001723538072985600000000000000000), (1673417825346363317827479892958605026619127567/22256831866140155118426568704000000000000000000), (1939447026864732471153149532763461975326839341/24729813184600172353807298560000000000000000000), (20188882025027433437183937211044407651085909391/247298131846001723538072985600000000000000000000)]
    reserve := (107230467/1562500000) }

theorem tilt_054_005_valid : tilt_054_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_054_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_054_005]
  · intro i; fin_cases i <;> norm_num [tilt_054_005]
  · norm_num [tilt_054_005]
  · norm_num [tilt_054_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_054_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_054_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_054_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_054_005]

def tilt_054_006 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11141347/50000000), (11141347/50000000), (17226061/100000000), (4776069/25000000), (4776069/25000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11141347/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4776069/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1990661/50000000), (1/100000000), (656481/12500000), (6503161/100000000), (1/100000000), (3413423/100000000), (1/100000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-3534878793137763157692849120965930789449/41441555267207180293279890000000000000000), (27417360434881/37513200000000), (-12769173742170421488472709573202530789449/20720777633603590146639945000000000000000), (27417360434881/37513200000000), (-22003468691203079819252570025439130789449/41441555267207180293279890000000000000000)]
    bernstein := [(724071093340151610745136633440110701849239/10609038148405038155079651840000000000000000), (2529960643786653444530677688101136940023919/35363460494683460516932172800000000000000000), (238083001613558866298110456758639349214534189/3182711444521511446523895552000000000000000000), (275981605028573382716793053277136028972421447/3536346049468346051693217280000000000000000000), (2873329023095555563410007237256988152149194797/35363460494683460516932172800000000000000000000)]
    reserve := (4265649977/62500000000) }

theorem tilt_054_006_valid : tilt_054_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_054_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_054_006]
  · intro i; fin_cases i <;> norm_num [tilt_054_006]
  · norm_num [tilt_054_006]
  · norm_num [tilt_054_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_054_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_054_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_054_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_054_006]

def tilt_054_007 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11141347/50000000), (11141347/50000000), (17226061/100000000), (4776069/25000000), (4776069/25000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11141347/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4776069/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1990661/50000000), (1/100000000), (5247731/100000000), (812491/12500000), (1/100000000), (3413423/100000000), (1/100000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-24622220686187456652499181725385656250843/289719376849764099880583630000000000000000), (191921523044167/262386550000000), (-89285459889668217367544914340852075350843/144859688424882049940291815000000000000000), (191921523044167/262386550000000), (-153948699093148978082590646956318494450843/289719376849764099880583630000000000000000)]
    bernstein := [(5095780271147659048040883844931484694106373/74168160473539609569429409280000000000000000), (53401652705106241462880372454925221040999399/741681604735396095694294092800000000000000000), (1674746151522654474350039706387435894739086023/22250448142061882870828822784000000000000000000), (5822803940145920176932688415538269448902962687/74168160473539609569429409280000000000000000000), (60611581461555194429434164123782679912740718037/741681604735396095694294092800000000000000000000)]
    reserve := (13741153181/200000000000) }

theorem tilt_054_007_valid : tilt_054_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_054_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_054_007]
  · intro i; fin_cases i <;> norm_num [tilt_054_007]
  · norm_num [tilt_054_007]
  · norm_num [tilt_054_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_054_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_054_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_054_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_054_007]

def tilt_054_008 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11141347/50000000), (11141347/50000000), (17226061/100000000), (4776069/25000000), (4776069/25000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11141347/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4776069/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1990661/50000000), (1/100000000), (2627983/50000000), (812491/12500000), (1/100000000), (3413423/100000000), (1/100000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-24744707607174300988616508069401134144247/290174018878549075208495180000000000000000), (191921523044167/262798300000000), (-89297339300042636440354434105076115044247/145087009439274537604247590000000000000000), (191921523044167/262798300000000), (-153849970992910971892092360140751095944247/290174018878549075208495180000000000000000)]
    bernstein := [(5064142206343283493855441955223920481712617/74284548832908563253374766080000000000000000), (53085180714596733222051499528437561680473971/742845488329085632533747660800000000000000000), (1665249357647131369469346440254664714386112467/22285364649872568976012429824000000000000000000), (5791139632467266284195166240736106808535606123/74284548832908563253374766080000000000000000000), (60294860714247482512617048047662230617875521273/742845488329085632533747660800000000000000000000)]
    reserve := (2130381707/31250000000) }

theorem tilt_054_008_valid : tilt_054_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_054_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_054_008]
  · intro i; fin_cases i <;> norm_num [tilt_054_008]
  · norm_num [tilt_054_008]
  · norm_num [tilt_054_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_054_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_054_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_054_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_054_008]

def tilt_054_009 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11141347/50000000), (11141347/50000000), (17226061/100000000), (4776069/25000000), (4776069/25000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11141347/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4776069/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1990661/50000000), (1/100000000), (656481/12500000), (6496697/100000000), (1/100000000), (3413423/100000000), (1/100000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-30778448158601421748991932108783664280661/362253178580884281914724637500000000000000), (27417360434881/37513200000000), (-111498215447053408782147364025517914280661/181126589290442140957362318750000000000000), (27417360434881/37513200000000), (-192217982735505395815302795942252164280661/362253178580884281914724637500000000000000)]
    bernstein := [(6364292830509227269725547478091575147888971/92736813716706376170169507200000000000000000), (22232398214709616550563107221714293218289491/309122712389021253900565024000000000000000000), (2091771769079263933842291687375573928741584521/27821044115011912851050852160000000000000000000), (2424308223636806541658981788564319914278747883/30912271238902125390056502400000000000000000000), (25236097024668129544908491243154476284517581033/309122712389021253900565024000000000000000000000)]
    reserve := (68627469237/1000000000000) }

theorem tilt_054_009_valid : tilt_054_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_054_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_054_009]
  · intro i; fin_cases i <;> norm_num [tilt_054_009]
  · norm_num [tilt_054_009]
  · norm_num [tilt_054_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_054_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_054_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_054_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_054_009]

def tilt_054_010 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11141347/50000000), (11141347/50000000), (17226061/100000000), (4776069/25000000), (4776069/25000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11141347/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4776069/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1990661/50000000), (1/100000000), (656481/12500000), (3251581/50000000), (1/100000000), (3413423/100000000), (1/100000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-61846786087908597167110770083749592089967/725227328695311044533899150000000000000000), (27417360434881/37513200000000), (-223446972545458949568803243946850592089967/362613664347655522266949575000000000000000), (27417360434881/37513200000000), (-385047159003009301970495717809951592089967/725227328695311044533899150000000000000000)]
    bernstein := [(12675177147886642536375426921267322385999537/185658196145999627400678182400000000000000000), (44287498707310699989988580178362943389821977/618860653819998758002260608000000000000000000), (4167646621500448243165656485808566840868385387/55697458843799888220203454720000000000000000000), (4831013175916844621301174844877289109125507201/61886065381999875800226060800000000000000000000), (50296694923878225809938802218508537262553350251/618860653819998758002260608000000000000000000000)]
    reserve := (13654314661/200000000000) }

theorem tilt_054_010_valid : tilt_054_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_054_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_054_010]
  · intro i; fin_cases i <;> norm_num [tilt_054_010]
  · norm_num [tilt_054_010]
  · norm_num [tilt_054_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_054_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_054_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_054_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_054_010]

def tilt_054_011 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11141347/50000000), (11141347/50000000), (17226061/100000000), (4776069/25000000), (4776069/25000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11141347/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(597/3125000), 0, 0, 0, 0], ![0, 0, 0, (4776069/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1990661/50000000), (1/100000000), (656481/12500000), (812491/12500000), (1/100000000), (3413423/100000000), (1/100000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-15405234003316420076791763736098473911839/181216668912440430019855650000000000000000), (27417360434881/37513200000000), (-55785189814068649030400337467309473911839/90608334456220215009927825000000000000000), (27417360434881/37513200000000), (-96165145624820877984008911198520473911839/181216668912440430019855650000000000000000)]
    bernstein := [(3181313989459841241462427693714990539478529/46391467241584750085083046400000000000000000), (11113630164598975100391879892579045654428009/154638224138615833616943488000000000000000000), (1045672851826020984239378517380215186199157979/13917440172475425025524913920000000000000000000), (1211937213562341635298846033815131855295329617/15463822413861583361694348800000000000000000000), (12616073725906821119062039448886743111161621467/154638224138615833616943488000000000000000000000)]
    reserve := (68575412217/1000000000000) }

theorem tilt_054_011_valid : tilt_054_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_054_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_054_011]
  · intro i; fin_cases i <;> norm_num [tilt_054_011]
  · norm_num [tilt_054_011]
  · norm_num [tilt_054_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_054_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_054_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_054_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_054_011]

def tilt_054_012 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11141347/50000000), (11141347/50000000), (17226061/100000000), (4776069/25000000), (4776069/25000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11141347/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5659/100000000), 0, 0], ![0, 0, 0, (4776069/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1990661/50000000), (1/100000000), (656481/12500000), (812491/12500000), (4967/100000000), (3413423/100000000), (1/100000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-76857945094614177221398748826663905372852047/900103194488091615908623013550000000000000000), (27417360434881/37513200000000), (-277425185606620498433972534549588942372852047/450051597244045807954311506775000000000000000), (27417360434881/37513200000000), (-477992426118626819646546320272513979372852047/900103194488091615908623013550000000000000000)]
    bernstein := [(15703283871406132542051375491687613013745758417/230426417788951453672607491468800000000000000000), (54871797809225977703371604885810680661831366457/768088059296504845575358304896000000000000000000), (5164012827183229519499969190304013497012584248267/69127925336685436101782247440640000000000000000000), (5986324661013668342618013048052509060693707745441/76808805929650484557535830489600000000000000000000), (62328216963072861869097861624010051057089173420491/768088059296504845575358304896000000000000000000000)]
    reserve := (34074400023/500000000000) }

theorem tilt_054_012_valid : tilt_054_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_054_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_054_012]
  · intro i; fin_cases i <;> norm_num [tilt_054_012]
  · norm_num [tilt_054_012]
  · norm_num [tilt_054_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_054_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_054_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_054_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_054_012]

def tilt_054_013 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11141347/50000000), (11141347/50000000), (17226061/100000000), (4776069/25000000), (4776069/25000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11141347/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (956169/10000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1990661/50000000), (1/100000000), (656481/12500000), (812491/12500000), (1/100000000), (341001/10000000), (1/100000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-85438364506953715112905236169157562577/1005752637224196276438975000000000000000), (27417360434881/37513200000000), (-309547147056551465351196132155657562577/502876318612098138219487500000000000000), (27417360434881/37513200000000), (-533655929606149215589487028142157562577/1005752637224196276438975000000000000000)]
    bernstein := [(17673835633909129976652632054552714415247/257472675129394246768377600000000000000000), (61739468342776758377729911112967884362887/858242250431314155894592000000000000000000), (5808810350113275280122534796749280242056597/77241802538818274030513280000000000000000000), (6732206349133726976025119511780970271384031/85824225043131415589459200000000000000000000), (70079140663897458571841468462306570066458581/858242250431314155894592000000000000000000000)]
    reserve := (34321769533/500000000000) }

theorem tilt_054_013_valid : tilt_054_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_054_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_054_013]
  · intro i; fin_cases i <;> norm_num [tilt_054_013]
  · norm_num [tilt_054_013]
  · norm_num [tilt_054_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_054_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_054_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_054_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_054_013]

def tilt_054_014 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11141347/50000000), (11141347/50000000), (17226061/100000000), (4776069/25000000), (4776069/25000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11141347/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4771293/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1990661/50000000), (1/100000000), (656481/12500000), (812491/12500000), (1/100000000), (3416837/100000000), (1/100000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-15472018178830334804405821349688494047343/181397916213951866378047350000000000000000), (27417360434881/37513200000000), (-55892360771161614496714995525297494047343/90698958106975933189023675000000000000000), (27417360434881/37513200000000), (-96312703363492894189024169700906494047343/181397916213951866378047350000000000000000)]
    bernstein := [(3169648079695938435417736881413265720317873/46437866550771677792780121600000000000000000), (11074962002423151902313444181300344893124633/154792888502572259309267072000000000000000000), (1042210992966855320985710510876114057030172523/13931359965231503337834036480000000000000000000), (1208109491066869289750024741783883836312793729/15479288850257225930926707200000000000000000000), (12577969084689441851183546392048343186441187179/154792888502572259309267072000000000000000000000)]
    reserve := (4265979893/62500000000) }

theorem tilt_054_014_valid : tilt_054_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_054_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_054_014]
  · intro i; fin_cases i <;> norm_num [tilt_054_014]
  · norm_num [tilt_054_014]
  · norm_num [tilt_054_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_054_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_054_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_054_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_054_014]

def tilt_054_015 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11141347/50000000), (11141347/50000000), (17226061/100000000), (4776069/25000000), (4776069/25000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11141347/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(597/3125000), 0, 0, 0, 0], ![0, 0, 0, (4776069/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1990661/50000000), (1/100000000), (656481/12500000), (812491/12500000), (1/100000000), (3413423/100000000), (1/100000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-15405234003316420076791763736098473911839/181216668912440430019855650000000000000000), (27417360434881/37513200000000), (-55785189814068649030400337467309473911839/90608334456220215009927825000000000000000), (27417360434881/37513200000000), (-96165145624820877984008911198520473911839/181216668912440430019855650000000000000000)]
    bernstein := [(3181313989459841241462427693714990539478529/46391467241584750085083046400000000000000000), (11113630164598975100391879892579045654428009/154638224138615833616943488000000000000000000), (1045672851826020984239378517380215186199157979/13917440172475425025524913920000000000000000000), (1211937213562341635298846033815131855295329617/15463822413861583361694348800000000000000000000), (12616073725906821119062039448886743111161621467/154638224138615833616943488000000000000000000000)]
    reserve := (68575412217/1000000000000) }

theorem tilt_054_015_valid : tilt_054_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_054_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_054_015]
  · intro i; fin_cases i <;> norm_num [tilt_054_015]
  · norm_num [tilt_054_015]
  · norm_num [tilt_054_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_054_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_054_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_054_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_054_015]

def tilt_054_016 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11141347/50000000), (11141347/50000000), (17226061/100000000), (4776069/25000000), (4776069/25000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11141347/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5659/100000000), 0, 0], ![0, 0, 0, (4776069/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1990661/50000000), (1/100000000), (656481/12500000), (812491/12500000), (4967/100000000), (3413423/100000000), (1/100000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-76857945094614177221398748826663905372852047/900103194488091615908623013550000000000000000), (27417360434881/37513200000000), (-277425185606620498433972534549588942372852047/450051597244045807954311506775000000000000000), (27417360434881/37513200000000), (-477992426118626819646546320272513979372852047/900103194488091615908623013550000000000000000)]
    bernstein := [(15703283871406132542051375491687613013745758417/230426417788951453672607491468800000000000000000), (54871797809225977703371604885810680661831366457/768088059296504845575358304896000000000000000000), (5164012827183229519499969190304013497012584248267/69127925336685436101782247440640000000000000000000), (5986324661013668342618013048052509060693707745441/76808805929650484557535830489600000000000000000000), (62328216963072861869097861624010051057089173420491/768088059296504845575358304896000000000000000000000)]
    reserve := (34074400023/500000000000) }

theorem tilt_054_016_valid : tilt_054_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_054_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_054_016]
  · intro i; fin_cases i <;> norm_num [tilt_054_016]
  · norm_num [tilt_054_016]
  · norm_num [tilt_054_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_054_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_054_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_054_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_054_016]

def tilt_054_017 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11141347/50000000), (11141347/50000000), (17226061/100000000), (4776069/25000000), (4776069/25000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11141347/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4776069/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1990661/50000000), (1/100000000), (656481/12500000), (812491/12500000), (1/100000000), (3413423/100000000), (1/100000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-15442738570603636320503517568441163925839/181216668912440430019855650000000000000000), (27417360434881/37513200000000), (-55822694381355865274112091299652163925839/90608334456220215009927825000000000000000), (27417360434881/37513200000000), (-96202650192108094227720665030863163925839/181216668912440430019855650000000000000000)]
    bernstein := [(3170475169513835747029730836167953125432529/46391467241584750085083046400000000000000000), (11077288238897662560235190429038979030862009/154638224138615833616943488000000000000000000), (1042382238596807918232352947884299907060811979/13917440172475425025524913920000000000000000000), (1208258128025167583439454118123810992991971617/15463822413861583361694348800000000000000000000), (12579046204213975836898217888040174666576363467/154638224138615833616943488000000000000000000000)]
    reserve := (34170886997/500000000000) }

theorem tilt_054_017_valid : tilt_054_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_054_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_054_017]
  · intro i; fin_cases i <;> norm_num [tilt_054_017]
  · norm_num [tilt_054_017]
  · norm_num [tilt_054_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_054_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_054_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_054_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_054_017]

def tilt_054_018 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11141347/50000000), (11141347/50000000), (17226061/100000000), (4776069/25000000), (4776069/25000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11141347/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4776069/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1990661/50000000), (1/100000000), (656481/12500000), (812491/12500000), (1/100000000), (3413423/100000000), (1/100000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-15442738570603636320503517568441163925839/181216668912440430019855650000000000000000), (27417360434881/37513200000000), (-55822694381355865274112091299652163925839/90608334456220215009927825000000000000000), (27417360434881/37513200000000), (-96202650192108094227720665030863163925839/181216668912440430019855650000000000000000)]
    bernstein := [(3170475169513835747029730836167953125432529/46391467241584750085083046400000000000000000), (11077288238897662560235190429038979030862009/154638224138615833616943488000000000000000000), (1042382238596807918232352947884299907060811979/13917440172475425025524913920000000000000000000), (1208258128025167583439454118123810992991971617/15463822413861583361694348800000000000000000000), (12579046204213975836898217888040174666576363467/154638224138615833616943488000000000000000000000)]
    reserve := (34170886997/500000000000) }

theorem tilt_054_018_valid : tilt_054_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_054_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_054_018]
  · intro i; fin_cases i <;> norm_num [tilt_054_018]
  · norm_num [tilt_054_018]
  · norm_num [tilt_054_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_054_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_054_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_054_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_054_018]

def tilt_054_019 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11141347/50000000), (11141347/50000000), (17226061/100000000), (4776069/25000000), (4776069/25000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11141347/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4776069/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1990661/50000000), (1/100000000), (656481/12500000), (812491/12500000), (1/100000000), (3413423/100000000), (1/100000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-15442738570603636320503517568441163925839/181216668912440430019855650000000000000000), (27417360434881/37513200000000), (-55822694381355865274112091299652163925839/90608334456220215009927825000000000000000), (27417360434881/37513200000000), (-96202650192108094227720665030863163925839/181216668912440430019855650000000000000000)]
    bernstein := [(3170475169513835747029730836167953125432529/46391467241584750085083046400000000000000000), (11077288238897662560235190429038979030862009/154638224138615833616943488000000000000000000), (1042382238596807918232352947884299907060811979/13917440172475425025524913920000000000000000000), (1208258128025167583439454118123810992991971617/15463822413861583361694348800000000000000000000), (12579046204213975836898217888040174666576363467/154638224138615833616943488000000000000000000000)]
    reserve := (34170886997/500000000000) }

theorem tilt_054_019_valid : tilt_054_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_054_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_054_019]
  · intro i; fin_cases i <;> norm_num [tilt_054_019]
  · norm_num [tilt_054_019]
  · norm_num [tilt_054_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_054_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_054_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_054_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_054_019]

def tilt_054_020 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11141347/50000000), (11141347/50000000), (17226061/100000000), (4776069/25000000), (4776069/25000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11141347/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4776069/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1990661/50000000), (1/100000000), (656481/12500000), (812491/12500000), (1/100000000), (3413423/100000000), (1/100000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-15442738570603636320503517568441163925839/181216668912440430019855650000000000000000), (27417360434881/37513200000000), (-55822694381355865274112091299652163925839/90608334456220215009927825000000000000000), (27417360434881/37513200000000), (-96202650192108094227720665030863163925839/181216668912440430019855650000000000000000)]
    bernstein := [(3170475169513835747029730836167953125432529/46391467241584750085083046400000000000000000), (11077288238897662560235190429038979030862009/154638224138615833616943488000000000000000000), (1042382238596807918232352947884299907060811979/13917440172475425025524913920000000000000000000), (1208258128025167583439454118123810992991971617/15463822413861583361694348800000000000000000000), (12579046204213975836898217888040174666576363467/154638224138615833616943488000000000000000000000)]
    reserve := (34170886997/500000000000) }

theorem tilt_054_020_valid : tilt_054_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_054_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_054_020]
  · intro i; fin_cases i <;> norm_num [tilt_054_020]
  · norm_num [tilt_054_020]
  · norm_num [tilt_054_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_054_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_054_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_054_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_054_020]

def tiltBundle054_row : Alternative → Row
  | .zero => tilt_054_000
  | (.spike 0 false false) => tilt_054_001
  | (.spike 0 false true) => tilt_054_002
  | (.spike 0 true false) => tilt_054_003
  | (.spike 0 true true) => tilt_054_004
  | (.spike 1 false false) => tilt_054_005
  | (.spike 1 false true) => tilt_054_006
  | (.spike 1 true false) => tilt_054_007
  | (.spike 1 true true) => tilt_054_008
  | (.spike 2 false false) => tilt_054_009
  | (.spike 2 false true) => tilt_054_010
  | (.spike 2 true false) => tilt_054_011
  | (.spike 2 true true) => tilt_054_012
  | (.spike 3 false false) => tilt_054_013
  | (.spike 3 false true) => tilt_054_014
  | (.spike 3 true false) => tilt_054_015
  | (.spike 3 true true) => tilt_054_016
  | (.spike 4 false false) => tilt_054_017
  | (.spike 4 false true) => tilt_054_018
  | (.spike 4 true false) => tilt_054_019
  | (.spike 4 true true) => tilt_054_020

def tiltBundle054 : TiltBundle where
  interval := ⟨(1/4), (11/40)⟩
  lambda := ![(11141347/50000000), (11141347/50000000), (17226061/100000000), (4776069/25000000), (4776069/25000000), 0, 0]
  row := tiltBundle054_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_054_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_054_001_valid | exact tilt_054_002_valid | exact tilt_054_003_valid | exact tilt_054_004_valid | exact tilt_054_005_valid | exact tilt_054_006_valid | exact tilt_054_007_valid | exact tilt_054_008_valid | exact tilt_054_009_valid | exact tilt_054_010_valid | exact tilt_054_011_valid | exact tilt_054_012_valid | exact tilt_054_013_valid | exact tilt_054_014_valid | exact tilt_054_015_valid | exact tilt_054_016_valid | exact tilt_054_017_valid | exact tilt_054_018_valid | exact tilt_054_019_valid | exact tilt_054_020_valid
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
