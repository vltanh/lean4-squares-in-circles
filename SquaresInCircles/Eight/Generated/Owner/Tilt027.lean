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

def tilt_027_000 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/160), (7/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14587971/100000000), (14587971/100000000), (8828353/100000000), (14553031/100000000), (1455303/10000000), (8263779/50000000), (8181043/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(221561/4000000), (1/100000000), (2118213/50000000), (2150511/50000000), (1/100000000), (1112893/20000000), (186497/100000000)]
    alternative := .zero
    polynomial := [(-22671334003366117585753174148084571780775127/3491231316290935131102718063050000000000000000), (17828086042069/28242840000000), (-25843835804269692768882782832088956548280775127/1745615658145467565551359031525000000000000000), (17828086042069/28242840000000), (-51665000274536019420179812490029828524780775127/3491231316290935131102718063050000000000000000)]
    bernstein := [(319079710760553559851698042994384083619524347973113/2288013355444427247519477309800448000000000000000000000), (53590809032422406884966671237632663092798005015541/269178041816991440884644389388288000000000000000000000), (6442158108126520001226900293721614894821443923313379/27456160265333126970233727717605376000000000000000000000), (264962471605360254766302098834391217279803839112701/1076712167267965763538577557553152000000000000000000000), (8545704349785492490177163377253819746222971112929673/36608213687110835960311636956807168000000000000000000000)]
    reserve := (139457101/1000000000000) }

theorem tilt_027_000_valid : tilt_027_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_027_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_027_000]
  · intro i; fin_cases i <;> norm_num [tilt_027_000]
  · norm_num [tilt_027_000]
  · norm_num [tilt_027_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_027_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_027_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_027_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_027_000]

def tilt_027_001 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/160), (7/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14587971/100000000), (14587971/100000000), (8828353/100000000), (14553031/100000000), (1455303/10000000), (8263779/50000000), (8181043/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(3647/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(221561/4000000), (1/100000000), (2118213/50000000), (2150511/50000000), (1/100000000), (1112893/20000000), (190547/100000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-11283330763687224704163236633704703151435001/1783523739323658869649993347775000000000000000), (4053604149286531174/6569321818212890625), (-12927687407473840109001707410865296203487935001/891761869661829434824996673887500000000000000), (4053604149286531174/6569321818212890625), (-25844091484183992993299251585096887703824435001/1783523739323658869649993347775000000000000000)]
    bernstein := [(174183234126163656345385963959932920221991996944119/1168850117803153076813819640397824000000000000000000000), (28408698833484077121986621514866150736179790945083/137511778565076832566331722399744000000000000000000000), (3374321542013818163360673217238514218871621073696877/14026201413637836921765835684773888000000000000000000000), (138041228453496002772498689718557893353886109226163/550047114260307330265326889598976000000000000000000000), (4446409308870146339015989445292433925197772763767399/18701601884850449229021114246365184000000000000000000000)]
    reserve := (149021017/1000000000000) }

theorem tilt_027_001_valid : tilt_027_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_027_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_027_001]
  · intro i; fin_cases i <;> norm_num [tilt_027_001]
  · norm_num [tilt_027_001]
  · norm_num [tilt_027_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_027_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_027_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_027_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_027_001]

def tilt_027_002 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/160), (7/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14587971/100000000), (14587971/100000000), (8828353/100000000), (14553031/100000000), (1455303/10000000), (8263779/50000000), (8181043/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (4321/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(221561/4000000), (3793/100000000), (2118213/50000000), (2150511/50000000), (1/100000000), (1112893/20000000), (3649/2000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-1720740437636046059430016154057232798344816827/259097653884198380450316908467050000000000000000), (2080693806461302784537/3220566348750000000000), (-1959633490245847754020812455354698914510641816827/129548826942099190225158454233525000000000000000), (2080693806461302784537/3220566348750000000000), (-3917546240054059461982194894555340596222938816827/259097653884198380450316908467050000000000000000)]
    bernstein := [(26637438460745932018576665203997850769683823713635413/169802238449548250611919689132965888000000000000000000000), (4368311868810779480338964402221551046212140297676641/19976733935240970660225845780348928000000000000000000000), (521334492155606946784383168654082606536275935925984279/2037626861394579007343036269595590656000000000000000000000), (21448694933742004585045000877806917009183022045609801/79906935740963882640903383121395712000000000000000000000), (696505297458946120238762779498743462442550430374167973/2716835815192772009790715026127454208000000000000000000000)]
    reserve := (31374661/200000000000) }

theorem tilt_027_002_valid : tilt_027_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_027_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_027_002]
  · intro i; fin_cases i <;> norm_num [tilt_027_002]
  · norm_num [tilt_027_002]
  · norm_num [tilt_027_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_027_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_027_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_027_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_027_002]

def tilt_027_003 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/160), (7/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14587971/100000000), (14587971/100000000), (8828353/100000000), (14553031/100000000), (1455303/10000000), (8263779/50000000), (8181043/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2768137/50000000), (1/100000000), (2118213/50000000), (2150511/50000000), (1/100000000), (1112893/20000000), (190547/100000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-558771722578818557676115251112455916014569087/89131896916879326099021463808700000000000000000), (4053604149286531174/6569321818212890625), (-646058223913031334563304380836209381836496569087/44565948458439663049510731904350000000000000000), (4053604149286531174/6569321818212890625), (-1291557676103483850568932646421306307756978569087/89131896916879326099021463808700000000000000000)]
    bernstein := [(12059109444334259677239428596535640984028165484294353/58413479963446035152254706521669632000000000000000000000), (30844340379828481757742576159158127856833584201341757/116826959926892070304509413043339264000000000000000000000), (208888407839397997466065585533097262123760727454576299/700961759561352421827056478260035584000000000000000000000), (2719168527513517173196357853735911033159526632296209/8817129051086193985245993437233152000000000000000000000), (5205510234679895464807774647831916895046599286276221/17634258102172387970491986874466304000000000000000000000)]
    reserve := (51610987/250000000000) }

theorem tilt_027_003_valid : tilt_027_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_027_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_027_003]
  · intro i; fin_cases i <;> norm_num [tilt_027_003]
  · norm_num [tilt_027_003]
  · norm_num [tilt_027_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_027_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_027_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_027_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_027_003]

def tilt_027_004 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/160), (7/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14587971/100000000), (14587971/100000000), (8828353/100000000), (14553031/100000000), (1455303/10000000), (8263779/50000000), (8181043/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5541777/100000000), (1/100000000), (2118213/50000000), (2150511/50000000), (1/100000000), (1112893/20000000), (3649/2000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-1249238281056648877786146148949132079231187/189842680620072614810004115050000000000000000), (2080693806461302784537/3220566348750000000000), (-1435825735874256611928759964641737124696231187/94921340310036307405002057525000000000000000), (2080693806461302784537/3220566348750000000000), (-2870402233467456574979733783134525117313231187/189842680620072614810004115050000000000000000)]
    bernstein := [(27098983506609803435079858531780926013807943384253/124415299171170788841884296839168000000000000000000000), (69575756845261919876444756426516271631661203964857/248830598342341577683768593678336000000000000000000000), (472974948818324355271720111885232967048291117737999/1492983590054049466102611562070016000000000000000000000), (327828978364860560946363855986023230285339560078177/995322393369366310735074374713344000000000000000000000), (631669848912680759025529442212564847363501658217613/1990644786738732621470148749426688000000000000000000000)]
    reserve := (2178107/10000000000) }

theorem tilt_027_004_valid : tilt_027_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_027_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_027_004]
  · intro i; fin_cases i <;> norm_num [tilt_027_004]
  · norm_num [tilt_027_004]
  · norm_num [tilt_027_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_027_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_027_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_027_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_027_004]

def tilt_027_005 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/160), (7/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14587971/100000000), (14587971/100000000), (8828353/100000000), (14553031/100000000), (1455303/10000000), (8263779/50000000), (8181043/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(221561/4000000), (1/100000000), (2118213/50000000), (859823/20000000), (1/100000000), (1112893/20000000), (190547/100000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-27105166905293364853267943918937744481429181/4278559092559358237030360403450000000000000000), (4053604149286531174/6569321818212890625), (-31012730357706420492597419890652517898948429181/2139279546279679118515180201725000000000000000), (4053604149286531174/6569321818212890625), (-61998355548507547620341571837386098053415429181/4278559092559358237030360403450000000000000000)]
    bernstein := [(393471067795036255580524513555200480283532963471539/2803996486899701014220216994004992000000000000000000000), (65281850418255157259544788297780302380358194662023/329881939635258942849437293412352000000000000000000000), (7802145682078563945439347673004569916398298785772737/33647957842796412170642603928059904000000000000000000000), (319675413507624205799499455229885636726357753057503/1319527758541035771397749173649408000000000000000000000), (10276418324863057377573496802765326687878541194805219/44863943790395216227523471904079872000000000000000000000)]
    reserve := (35081273/250000000000) }

theorem tilt_027_005_valid : tilt_027_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_027_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_027_005]
  · intro i; fin_cases i <;> norm_num [tilt_027_005]
  · norm_num [tilt_027_005]
  · norm_num [tilt_027_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_027_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_027_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_027_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_027_005]

def tilt_027_006 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/160), (7/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14587971/100000000), (14587971/100000000), (8828353/100000000), (14553031/100000000), (1455303/10000000), (8263779/50000000), (8181043/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(221561/4000000), (1/100000000), (2118213/50000000), (430293/10000000), (1/100000000), (1112893/20000000), (3649/2000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-179647378885300198810200655549537377553087/27335891760397210905634403100000000000000000), (2080693806461302784537/3220566348750000000000), (-206747673768579482098310562096498931431553087/13667945880198605452817201550000000000000000), (2080693806461302784537/3220566348750000000000), (-413315700158273663997810923537448325485553087/27335891760397210905634403100000000000000000)]
    bernstein := [(4055091066753398207025997377707285513294492190353/17914850024093916139116562415616000000000000000000000), (607322588220060588252731456186342320784698386221/2107629414599284251660772048896000000000000000000000), (69941530964262252754176153583826622481215172344299/214978200289126993669398748987392000000000000000000000), (2848791114623692789169199211896711104762323080181/8430517658397137006643088195584000000000000000000000), (93404961482682627717007820458469847243793121655713/286637600385502658225864998649856000000000000000000000)]
    reserve := (45270723/200000000000) }

theorem tilt_027_006_valid : tilt_027_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_027_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_027_006]
  · intro i; fin_cases i <;> norm_num [tilt_027_006]
  · norm_num [tilt_027_006]
  · norm_num [tilt_027_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_027_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_027_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_027_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_027_006]

def tilt_027_007 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/160), (7/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14587971/100000000), (14587971/100000000), (8828353/100000000), (14553031/100000000), (1455303/10000000), (8263779/50000000), (8181043/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(221561/4000000), (1/100000000), (2117243/50000000), (2150511/50000000), (1/100000000), (1112893/20000000), (190547/100000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-135523177637575782071755653403747403965106747/21392484055664891922508421196300000000000000000), (3112444722220503882677/5042928774012500000000), (-155064647056926254727644604693395052042103856747/10696242027832445961254210598150000000000000000), (3112444722220503882677/5042928774012500000000), (-309993770936214933673217453733386356680242606747/21392484055664891922508421196300000000000000000)]
    bernstein := [(2002900204140265049142516169121073569863324805915893/14019778350720543570335118915207168000000000000000000000), (330754572624140167829597528644785655084427217840001/1649385688320063949451190460612608000000000000000000000), (39470611891287608879750025753081941751100232045264119/168237340208646522844021426982486016000000000000000000000), (1617064161650972614468241762185066125760767487686761/6597542753280255797804761842450432000000000000000000000), (52039605101748478827767797291885944956421051330986053/224316453611528697125361902643314688000000000000000000000)]
    reserve := (17857809/125000000000) }

theorem tilt_027_007_valid : tilt_027_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_027_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_027_007]
  · intro i; fin_cases i <;> norm_num [tilt_027_007]
  · norm_num [tilt_027_007]
  · norm_num [tilt_027_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_027_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_027_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_027_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_027_007]

def tilt_027_008 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/160), (7/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14587971/100000000), (14587971/100000000), (8828353/100000000), (14553031/100000000), (1455303/10000000), (8263779/50000000), (8181043/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(221561/4000000), (1/100000000), (847673/20000000), (2150511/50000000), (1/100000000), (1112893/20000000), (3649/2000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-53895248484171383438091537916681676641439/8200882957092950922783728655000000000000000), (2497437627905194303981/3866448471250000000000), (-62023929454970440320644264460935382014536439/4100441478546475461391864327500000000000000), (2497437627905194303981/3866448471250000000000), (-123993963661456709257850437383954082352431439/8200882957092950922783728655000000000000000)]
    bernstein := [(1202917597134434302384127593257852022392805962241/5374530654760436316755544411340800000000000000000000), (180533040224166096929864360507438969402826089437/632297724089463096088887577804800000000000000000000), (20806382563784117978741343637653852155411614051003/64494367857125235801066532936089600000000000000000000), (847482682552760485706725127526060715220595243557/2529190896357852384355550311219200000000000000000000), (27769752650734228661174781015797223069478185542161/85992490476166981068088710581452800000000000000000000)]
    reserve := (111909083/500000000000) }

theorem tilt_027_008_valid : tilt_027_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_027_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_027_008]
  · intro i; fin_cases i <;> norm_num [tilt_027_008]
  · norm_num [tilt_027_008]
  · norm_num [tilt_027_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_027_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_027_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_027_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_027_008]

def tilt_027_009 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/160), (7/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14587971/100000000), (14587971/100000000), (8828353/100000000), (14553031/100000000), (1455303/10000000), (8263779/50000000), (8181043/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(221561/4000000), (1/100000000), (2118213/50000000), (1074779/25000000), (1/100000000), (1112893/20000000), (190547/100000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-135527531187177336382689558632367355584252539/21392800438889652808251250427400000000000000000), (4053604149286531174/6569321818212890625), (-155063689522406507888041493220122560313148252539/10696400219444826404125625213700000000000000000), (4053604149286531174/6569321818212890625), (-309991851513625838439700296881612753270712252539/21392800438889652808251250427400000000000000000)]
    bernstein := [(1966263765250738195187442244153756025365238858533141/14019985695630722864415539480100864000000000000000000000), (326280846215224777882442549881276766002908647720737/1649410081838908572284181115305984000000000000000000000), (38997631530603487725374169292701363302364772216815703/168239828347568674372986473761210368000000000000000000000), (1597863446905280078170045493125905134368883011182857/6597640327355634289136724461223936000000000000000000000), (51364626639509143247344064252169774542235123697641061/224319771130091565830648631681613824000000000000000000000)]
    reserve := (140247201/1000000000000) }

theorem tilt_027_009_valid : tilt_027_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_027_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_027_009]
  · intro i; fin_cases i <;> norm_num [tilt_027_009]
  · norm_num [tilt_027_009]
  · norm_num [tilt_027_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_027_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_027_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_027_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_027_009]

def tilt_027_010 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/160), (7/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14587971/100000000), (14587971/100000000), (8828353/100000000), (14553031/100000000), (1455303/10000000), (8263779/50000000), (8181043/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(221561/4000000), (1/100000000), (2118213/50000000), (4302931/100000000), (1/100000000), (1112893/20000000), (3649/2000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-267126981493601021286250126989861173386427/41003847169878802741176017655000000000000000), (2080693806461302784537/3220566348750000000000), (-310119238575581760420230338139855217026086427/20501923584939401370588008827500000000000000), (2080693806461302784537/3220566348750000000000), (-619971350169669919819174426152720572878786427/41003847169878802741176017655000000000000000)]
    bernstein := [(7619980177371389837875050225694705011293353057813/26872281281251772164457114930380800000000000000000000), (1091858471762915059534488786414465694180751473441/3161444856617855548759660580044800000000000000000000), (123362647992807092092622159751203820536420927963479/322467375375021265973485379164569600000000000000000000), (4996776993894839095943699309827844709363218254601/12645779426471422195038642320179200000000000000000000), (164711193056974765618207105150884220915092532758373/429956500500028354631313838886092800000000000000000000)]
    reserve := (283562831/1000000000000) }

theorem tilt_027_010_valid : tilt_027_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_027_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_027_010]
  · intro i; fin_cases i <;> norm_num [tilt_027_010]
  · norm_num [tilt_027_010]
  · norm_num [tilt_027_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_027_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_027_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_027_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_027_010]

def tilt_027_011 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/160), (7/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14587971/100000000), (14587971/100000000), (8828353/100000000), (14553031/100000000), (1455303/10000000), (8263779/50000000), (8181043/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(14553/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(221561/4000000), (1/100000000), (2118213/50000000), (2150511/50000000), (1/100000000), (1112893/20000000), (190547/100000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-11284007016973442046615076583744065843267501/1783523739323658869649993347775000000000000000), (4053604149286531174/6569321818212890625), (-12927688083727126326344159250815335566179767501/891761869661829434824996673887500000000000000), (4053604149286531174/6569321818212890625), (-25844092160437279210641703425046927066516267501/1783523739323658869649993347775000000000000000)]
    bernstein := [(173739733100217453661141587854122094985870342511619/1168850117803153076813819640397824000000000000000000000), (28356519186048569734442074472544778701487513042583/137511778565076832566331722399744000000000000000000000), (3368998888917986122620683120572284567880152643299377/14026201413637836921765835684773888000000000000000000000), (137832483375589005375234005430269313417840610423663/550047114260307330265326889598976000000000000000000000), (4439311491250997989745372239633331128693316969934899/18701601884850449229021114246365184000000000000000000000)]
    reserve := (9290099/62500000000) }

theorem tilt_027_011_valid : tilt_027_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_027_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_027_011]
  · intro i; fin_cases i <;> norm_num [tilt_027_011]
  · norm_num [tilt_027_011]
  · norm_num [tilt_027_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_027_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_027_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_027_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_027_011]

def tilt_027_012 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/160), (7/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14587971/100000000), (14587971/100000000), (8828353/100000000), (14553031/100000000), (1455303/10000000), (8263779/50000000), (8181043/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (539/12500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(221561/4000000), (1/100000000), (2118213/50000000), (2150511/50000000), (473/12500000), (1112893/20000000), (3649/2000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-156052230138033848142716220359174830619248403/23498442640697137588955712236400000000000000000), (2080693806461302784537/3220566348750000000000), (-177725782241744895840949349250947294658995248403/11749221320348568794477856118200000000000000000), (2080693806461302784537/3220566348750000000000), (-355295512253351757833755982281535414487371248403/23498442640697137588955712236400000000000000000)]
    bernstein := [(2420784703085797387238553354362742105118548629896957/15399939369007276090298015571247104000000000000000000000), (396758814267749769483299676766547957271555015737449/1811757572824385422388001831911424000000000000000000000), (47340939357429188501364167461114470834628895248052431/184799272428087313083576186854965248000000000000000000000), (1947582329578510095681326026548973713014034603852689/7247030291297541689552007327645696000000000000000000000), (63247566380014728053087336656960591831292207251118797/246399029904116417444768249139953664000000000000000000000)]
    reserve := (15719443/100000000000) }

theorem tilt_027_012_valid : tilt_027_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_027_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_027_012]
  · intro i; fin_cases i <;> norm_num [tilt_027_012]
  · norm_num [tilt_027_012]
  · norm_num [tilt_027_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_027_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_027_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_027_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_027_012]

def tilt_027_013 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/160), (7/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14587971/100000000), (14587971/100000000), (8828353/100000000), (14553031/100000000), (1455303/10000000), (8263779/50000000), (8181043/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(221561/4000000), (1/100000000), (2118213/50000000), (2150511/50000000), (1/100000000), (1112341/20000000), (190547/100000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-22348508861210525555268333118751022875225819/3565278206841121348998229390350000000000000000), (4053604149286531174/6569321818212890625), (-25842343471704625246417767395129101921076225819/1782639103420560674499114695175000000000000000), (4053604149286531174/6569321818212890625), (-51662338434548039967280266457139452819277225819/3565278206841121348998229390350000000000000000)]
    bernstein := [(483922037992394787490020069578853847344388467473461/2336540725635397287279479613259776000000000000000000000), (72758193759335869266701023000257726048784775702977/274887144192399680856409366265856000000000000000000000), (8374232164133475685682457151288443390672210687662263/28038488707624767447353755359117312000000000000000000000), (339829536268968181536568818892469352024379204707497/1099548576769598723425637465063424000000000000000000000), (11060612754373828936718770277680369023513769564539781/37384651610166356596471673812156416000000000000000000000)]
    reserve := (41422093/200000000000) }

theorem tilt_027_013_valid : tilt_027_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_027_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_027_013]
  · intro i; fin_cases i <;> norm_num [tilt_027_013]
  · norm_num [tilt_027_013]
  · norm_num [tilt_027_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_027_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_027_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_027_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_027_013]

def tilt_027_014 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/160), (7/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14587971/100000000), (14587971/100000000), (8828353/100000000), (14553031/100000000), (1455303/10000000), (8263779/50000000), (8181043/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(221561/4000000), (1/100000000), (2118213/50000000), (2150511/50000000), (1/100000000), (222689/4000000), (3649/2000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-44979467208722728068437064033556350570907/6834330806785135981630130025000000000000000), (2080693806461302784537/3220566348750000000000), (-51689690341326482114091804924829172309070907/3417165403392567990815065012500000000000000), (2080693806461302784537/3220566348750000000000), (-103334401215444241500115172785624788267570907/6834330806785135981630130025000000000000000)]
    bernstein := [(971020004304641811870038240109609838782700490933/4478947037534706716921122013184000000000000000000000), (146802320532984271492014015038353658892653865281/526934945592318437284837883904000000000000000000000), (16972566337167549282751398577134706331476306192439/53747364450416480603053464158208000000000000000000000), (692087407858763237771508619669395105191592204841/2107739782369273749139351535616000000000000000000000), (22667395738119365332407495881897931046538317605893/71663152600555307470737952210944000000000000000000000)]
    reserve := (216796491/1000000000000) }

theorem tilt_027_014_valid : tilt_027_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_027_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_027_014]
  · intro i; fin_cases i <;> norm_num [tilt_027_014]
  · norm_num [tilt_027_014]
  · norm_num [tilt_027_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_027_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_027_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_027_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_027_014]

def tilt_027_015 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/160), (7/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14587971/100000000), (14587971/100000000), (8828353/100000000), (14553031/100000000), (1455303/10000000), (8263779/50000000), (8181043/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(14553/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(221561/4000000), (1/100000000), (2118213/50000000), (2150511/50000000), (1/100000000), (1112893/20000000), (190547/100000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-22568014033402909352736437212244883715463627/3567047478647317739299986695550000000000000000), (4053604149286531174/6569321818212890625), (-25855376167453708677947824785675427884388463627/1783523739323658869649993347775000000000000000), (4053604149286531174/6569321818212890625), (-51688184320874014446542913134138610885061463627/3567047478647317739299986695550000000000000000)]
    bernstein := [(347479466557184900874618348439627643661232351404613/2337700235606306153627639280795648000000000000000000000), (56713038414070185295475811073234285661260722161041/275023557130153665132663444799488000000000000000000000), (6737997782117487611678717874968277274892441935627879/28052402827275673843531671369547776000000000000000000000), (275664966919091501003445057733368462648602899838201/1100094228520614660530653779197952000000000000000000000), (8878622988211444755769285957884167683605689064641173/37403203769700898458042228492730368000000000000000000000)]
    reserve := (9290099/62500000000) }

theorem tilt_027_015_valid : tilt_027_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_027_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_027_015]
  · intro i; fin_cases i <;> norm_num [tilt_027_015]
  · norm_num [tilt_027_015]
  · norm_num [tilt_027_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_027_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_027_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_027_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_027_015]

def tilt_027_016 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/160), (7/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14587971/100000000), (14587971/100000000), (8828353/100000000), (14553031/100000000), (1455303/10000000), (8263779/50000000), (8181043/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (539/12500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(221561/4000000), (1/100000000), (2118213/50000000), (2150511/50000000), (473/12500000), (1112893/20000000), (3649/2000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-39013057481961199114684160646951060468531257/5874610660174284397238928059100000000000000000), (2080693806461302784537/3220566348750000000000), (-44431445560383676697316342418293981017562531257/2937305330087142198619464029550000000000000000), (2080693806461302784537/3220566348750000000000), (-88823878063285392195518000675941010974656531257/5874610660174284397238928059100000000000000000)]
    bernstein := [(605196210233041609795143408597754548358511219022583/3849984842251819022574503892811776000000000000000000000), (99189707621479887931968531825136890271602196374331/452939393206096355597000457977856000000000000000000000), (11835235252946195492695154338587655966787720150369389/46199818107021828270894046713741312000000000000000000000), (486895598614855529906258406191674735716001855091891/1811757572824385422388001831911424000000000000000000000), (15811892146529118118566299790676235916078931756285543/61599757476029104361192062284988416000000000000000000000)]
    reserve := (157194439/1000000000000) }

theorem tilt_027_016_valid : tilt_027_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_027_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_027_016]
  · intro i; fin_cases i <;> norm_num [tilt_027_016]
  · norm_num [tilt_027_016]
  · norm_num [tilt_027_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_027_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_027_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_027_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_027_016]

def tilt_027_017 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/160), (7/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14587971/100000000), (14587971/100000000), (8828353/100000000), (14553031/100000000), (1455303/10000000), (8263779/50000000), (8181043/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(221561/4000000), (1/100000000), (2118213/50000000), (2150511/50000000), (1/100000000), (2780853/50000000), (190547/100000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-1163990168247134779015135109945385636384667/185691606660501606273124525865625000000000000), (4053604149286531174/6569321818212890625), (-1345955636277818419513092543028782593349572167/92845803330250803136562262932812500000000000), (4053604149286531174/6569321818212890625), (-2690747282387389704247169950947619801062759667/185691606660501606273124525865625000000000000)]
    bernstein := [(25200917940650722628453853830732124703913616793373/121694851341026332687154889271296000000000000000000000), (3789094692596508986582464502524022659420463332361/14317041334238392080841751678976000000000000000000000), (436117685944660582508650217624113778024601696294959/1460338216092315992245858671255552000000000000000000000), (17697877007522788048636429194170492357719579932721/57268165336953568323367006715904000000000000000000000), (576019920440621453801247410325680120295362421841133/1947117621456421322994478228340736000000000000000000000)]
    reserve := (10354143/50000000000) }

theorem tilt_027_017_valid : tilt_027_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_027_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_027_017]
  · intro i; fin_cases i <;> norm_num [tilt_027_017]
  · norm_num [tilt_027_017]
  · norm_num [tilt_027_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_027_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_027_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_027_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_027_017]

def tilt_027_018 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/160), (7/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14587971/100000000), (14587971/100000000), (8828353/100000000), (14553031/100000000), (1455303/10000000), (8263779/50000000), (8181043/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(221561/4000000), (1/100000000), (2118213/50000000), (2150511/50000000), (1/100000000), (2783613/50000000), (3649/2000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-9114780047076682439182907356149057457607/1389091876907744993244133950000000000000000), (2080693806461302784537/3220566348750000000000), (-10506009119616242763072665819019191100457607/694545938453872496622066975000000000000000), (2080693806461302784537/3220566348750000000000), (-21002903459185408843706148730682233143457607/1389091876907744993244133950000000000000000)]
    bernstein := [(215324579781496548571857047313378187498064708233/910355252450259758772475625472000000000000000000000), (31951264442270545974936398383753859925987661381/107100617935324677502644191232000000000000000000000), (3665288235980771456986349885381886586106223928339/10924263029403117105269707505664000000000000000000000), (2813638238625610253764153729407941961670800697/8083065504552805849256165376000000000000000000000), (92352304025566039642416325587107001668083943381/274824227154795398874709622784000000000000000000000)]
    reserve := (236528079/1000000000000) }

theorem tilt_027_018_valid : tilt_027_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_027_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_027_018]
  · intro i; fin_cases i <;> norm_num [tilt_027_018]
  · norm_num [tilt_027_018]
  · norm_num [tilt_027_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_027_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_027_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_027_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_027_018]

def tilt_027_019 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/160), (7/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14587971/100000000), (14587971/100000000), (8828353/100000000), (14553031/100000000), (1455303/10000000), (8263779/50000000), (8181043/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(221561/4000000), (1/100000000), (2118213/50000000), (2150511/50000000), (1/100000000), (1112893/20000000), (186497/100000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-22100097014368401182398593661894069585999127/3491231316290935131102718063050000000000000000), (17828086042069/28242840000000), (-25843861117415783810182542234033746512685260127/1745615658145467565551359031525000000000000000), (17828086042069/28242840000000), (-51665622137817199219182685874405598955784521127/3491231316290935131102718063050000000000000000)]
    bernstein := [(693433869201452454559507545263897948985425716547113/2288013355444427247519477309800448000000000000000000000), (97632359387826489566685753878120293425968663133541/269178041816991440884644389388288000000000000000000000), (10934383814531317609292032206875760329507049839355379/27456160265333126970233727717605376000000000000000000000), (441127671956463999659399156315848398280998869310701/1076712167267965763538577557553152000000000000000000000), (14535302803960796313467737806738497564520633006783673/36608213687110835960311636956807168000000000000000000000)]
    reserve := (151536237/500000000000) }

theorem tilt_027_019_valid : tilt_027_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_027_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_027_019]
  · intro i; fin_cases i <;> norm_num [tilt_027_019]
  · norm_num [tilt_027_019]
  · norm_num [tilt_027_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_027_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_027_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_027_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_027_019]

def tilt_027_020 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/160), (7/320)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14587971/100000000), (14587971/100000000), (8828353/100000000), (14553031/100000000), (1455303/10000000), (8263779/50000000), (8181043/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(221561/4000000), (1/100000000), (2118213/50000000), (2150511/50000000), (1/100000000), (1112893/20000000), (186497/100000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-22665558274515163062573694850074554712999127/3491231316290935131102718063050000000000000000), (17828086042069/28242840000000), (-25843284102135069662430006856266299447366260127/1745615658145467565551359031525000000000000000), (17828086042069/28242840000000), (-51663902645995624161797440017682524340019521127/3491231316290935131102718063050000000000000000)]
    bernstein := [(323119205671861215631969737567569392897577881547113/2288013355444427247519477309800448000000000000000000000), (54068537866688580814854489363885843158640968133541/269178041816991440884644389388288000000000000000000000), (6491155004591744555757922245636853315913166134355379/27456160265333126970233727717605376000000000000000000000), (266895005330271813283530199409551665802654574310701/1076712167267965763538577557553152000000000000000000000), (8611806333009172678041893770036970731270793571783673/36608213687110835960311636956807168000000000000000000000)]
    reserve := (35305651/250000000000) }

theorem tilt_027_020_valid : tilt_027_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_027_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_027_020]
  · intro i; fin_cases i <;> norm_num [tilt_027_020]
  · norm_num [tilt_027_020]
  · norm_num [tilt_027_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_027_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_027_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_027_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_027_020]

def tiltBundle027_row : Alternative → Row
  | .zero => tilt_027_000
  | (.spike 0 false false) => tilt_027_001
  | (.spike 0 false true) => tilt_027_002
  | (.spike 0 true false) => tilt_027_003
  | (.spike 0 true true) => tilt_027_004
  | (.spike 1 false false) => tilt_027_005
  | (.spike 1 false true) => tilt_027_006
  | (.spike 1 true false) => tilt_027_007
  | (.spike 1 true true) => tilt_027_008
  | (.spike 2 false false) => tilt_027_009
  | (.spike 2 false true) => tilt_027_010
  | (.spike 2 true false) => tilt_027_011
  | (.spike 2 true true) => tilt_027_012
  | (.spike 3 false false) => tilt_027_013
  | (.spike 3 false true) => tilt_027_014
  | (.spike 3 true false) => tilt_027_015
  | (.spike 3 true true) => tilt_027_016
  | (.spike 4 false false) => tilt_027_017
  | (.spike 4 false true) => tilt_027_018
  | (.spike 4 true false) => tilt_027_019
  | (.spike 4 true true) => tilt_027_020

def tiltBundle027 : TiltBundle where
  interval := ⟨(3/160), (7/320)⟩
  lambda := ![(14587971/100000000), (14587971/100000000), (8828353/100000000), (14553031/100000000), (1455303/10000000), (8263779/50000000), (8181043/50000000)]
  row := tiltBundle027_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_027_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_027_001_valid | exact tilt_027_002_valid | exact tilt_027_003_valid | exact tilt_027_004_valid | exact tilt_027_005_valid | exact tilt_027_006_valid | exact tilt_027_007_valid | exact tilt_027_008_valid | exact tilt_027_009_valid | exact tilt_027_010_valid | exact tilt_027_011_valid | exact tilt_027_012_valid | exact tilt_027_013_valid | exact tilt_027_014_valid | exact tilt_027_015_valid | exact tilt_027_016_valid | exact tilt_027_017_valid | exact tilt_027_018_valid | exact tilt_027_019_valid | exact tilt_027_020_valid
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
