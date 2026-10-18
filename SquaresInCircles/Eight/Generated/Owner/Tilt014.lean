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

def tilt_014_000 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/40), (-1/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(15738641/100000000), (15738641/100000000), (806701/10000000), (13093241/100000000), (13093241/100000000), (601317/4000000), (9618151/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(180277/25000000), 0, (130933/3125000), 0, 0]] i.1) i.2
    mu := ![(6280257/100000000), (1/100000000), (569823/12500000), (1942983/50000000), (1/100000000), (503733/10000000), (60743/100000000)]
    alternative := .zero
    polynomial := [(-1858910419570520297044706778563332199298661/112569627183898468952004162300000000000000000), (-1889357050478116097/814417846800000000), (-181364964614231793742431166086349398221015719/2962358610102591288210635850000000000000000), (-1889357050478116097/814417846800000000), (-6890009744921237641915339604502713800199298661/112569627183898468952004162300000000000000000)]
    bernstein := [(931276685177163400393337714296302489587472826139/288178245590780080517130655488000000000000000000000), (1065574508194683199716527500679707019607174269513/192118830393853387011420436992000000000000000000000), (21666866045562826806018893151819583719634124035217/3458138947089360966205567865856000000000000000000000), (4142513933193784361919381712895751858184152091913/768475321575413548045681747968000000000000000000000), (13473241846258261766765337191847906174435623280539/4610851929452481288274090487808000000000000000000000)]
    reserve := (1461036057/500000000000) }

theorem tilt_014_000_valid : tilt_014_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_014_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_014_000]
  · intro i; fin_cases i <;> norm_num [tilt_014_000]
  · norm_num [tilt_014_000]
  · norm_num [tilt_014_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_014_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_014_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_014_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_014_000]

def tilt_014_001 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/40), (-1/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(15738641/100000000), (15738641/100000000), (806701/10000000), (13093241/100000000), (13093241/100000000), (601317/4000000), (9618151/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(15739/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(140377/20000000), 0, (4190577/100000000), 0, 0]] i.1) i.2
    mu := ![(6280257/100000000), (1/100000000), (569823/12500000), (1942983/50000000), (1/100000000), (503733/10000000), (60743/100000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-1862222389637650391991745892457785667475411/112569627183898468952004162300000000000000000), (-236169793149947803363/101802230850000000000), (-3445941046787568886856810775879028404432475411/56284813591949234476002081150000000000000000), (-236169793149947803363/101802230850000000000), (-6890019871185500123321629805865599023197475411/112569627183898468952004162300000000000000000)]
    bernstein := [(922787990952715927514596049244558320551589049389/288178245590780080517130655488000000000000000000000), (1059918009385860028812895974939614999718172077263/192118830393853387011420436992000000000000000000000), (21565085648909765498993473275798711371393213104967/3458138947089360966205567865856000000000000000000000), (4119901805977990831918414220303909779216067099663/768475321575413548045681747968000000000000000000000), (13337589178121578399775310257388384975135802703789/4610851929452481288274090487808000000000000000000000)]
    reserve := (2892651809/1000000000000) }

theorem tilt_014_001_valid : tilt_014_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_014_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_014_001]
  · intro i; fin_cases i <;> norm_num [tilt_014_001]
  · norm_num [tilt_014_001]
  · norm_num [tilt_014_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_014_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_014_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_014_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_014_001]

def tilt_014_002 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/40), (-1/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(15738641/100000000), (15738641/100000000), (806701/10000000), (13093241/100000000), (13093241/100000000), (601317/4000000), (9618151/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2331/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(740331/100000000), 0, (837827/20000000), 0, 0]] i.1) i.2
    mu := ![(6280257/100000000), (1023/25000000), (569823/12500000), (1942983/50000000), (1/100000000), (503733/10000000), (7593/12500000)]
    alternative := (.spike 0 false true)
    polynomial := [(-52634955793225265139652545131560073291583061/3198906234569726075329673686200000000000000000), (-3936166585367420831/1696731780000000000), (-97921884264798205437935573776654800555198333061/1599453117284863037664836843100000000000000000), (-3936166585367420831/1696731780000000000), (-195791133573803185610731495008178041037105083061/3198906234569726075329673686200000000000000000)]
    bernstein := [(26948826246442785550843053252278742207135192961739/8189199960498498752843964636672000000000000000000000), (927373789961223797512686075455088693180405291961/165438383040373712178665952256000000000000000000000), (621517018630627304008620207525074881919119923162017/98270399525981985034127575640064000000000000000000000), (3606324909118207992518438027099340801869314224761/661753532161494848714663809024000000000000000000000), (390616334497100916526731160772331786367861253176139/131027199367975980045503434186752000000000000000000000)]
    reserve := (29811851/10000000000) }

theorem tilt_014_002_valid : tilt_014_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_014_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_014_002]
  · intro i; fin_cases i <;> norm_num [tilt_014_002]
  · norm_num [tilt_014_002]
  · norm_num [tilt_014_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_014_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_014_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_014_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_014_002]

def tilt_014_003 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/40), (-1/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(15738641/100000000), (15738641/100000000), (806701/10000000), (13093241/100000000), (13093241/100000000), (601317/4000000), (9618151/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(140377/20000000), 0, (4190577/100000000), 0, 0]] i.1) i.2
    mu := ![(313859/5000000), (1/100000000), (569823/12500000), (1942983/50000000), (1/100000000), (503733/10000000), (60743/100000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-556013633530971827908498257085381589048011/33754342172600124071489820600000000000000000), (-236169793149947803363/101802230850000000000), (-1033273434987507695976883582492544281919048011/16877171086300062035744910300000000000000000), (-236169793149947803363/101802230850000000000), (-2065990856341484420125858666728003182249048011/33754342172600124071489820600000000000000000)]
    bernstein := [(282799554263724145369836740081240727020609156789/86411115961856317623013940736000000000000000000000), (321884203212680898583854710979126345613301393063/57607410641237545082009293824000000000000000000000), (6539499573930530414399775019278093196346396307167/1036933391542275811476167288832000000000000000000000), (1251615731390908565906397984597392348924128255463/230429642564950180328037175296000000000000000000000), (4096805611279000720267890030142220346772845851189/1382577855389701081968223051776000000000000000000000)]
    reserve := (2963164493/1000000000000) }

theorem tilt_014_003_valid : tilt_014_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_014_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_014_003]
  · intro i; fin_cases i <;> norm_num [tilt_014_003]
  · norm_num [tilt_014_003]
  · norm_num [tilt_014_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_014_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_014_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_014_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_014_003]

def tilt_014_004 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/40), (-1/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(15738641/100000000), (15738641/100000000), (806701/10000000), (13093241/100000000), (13093241/100000000), (601317/4000000), (9618151/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(740331/100000000), 0, (837827/20000000), 0, 0]] i.1) i.2
    mu := ![(785417/12500000), (1/100000000), (569823/12500000), (1942983/50000000), (1/100000000), (503733/10000000), (7593/12500000)]
    alternative := (.spike 0 true true)
    polynomial := [(-6789450048744966576044461752830271558757/414068641279217970568275600000000000000000), (-3936166585367420831/1696731780000000000), (-12675052947883828535211456251413541978058757/207034320639608985284137800000000000000000), (-3936166585367420831/1696731780000000000), (-25343316445718912103846868041074253684558757/414068641279217970568275600000000000000000)]
    bernstein := [(3548907606647667763359131566167059690909498843/1060015721674798004654785536000000000000000000000), (1333908729655792268645247424417818449088618627/235559049261066223256619008000000000000000000000), (81176771534629854175676816590881547961909138129/12720188660097576055857426432000000000000000000000), (5188710961830363730090987412925014250778668227/942236197044264893026476032000000000000000000000), (51530866092807125405117867309166326390076631643/16960251546796768074476568576000000000000000000000)]
    reserve := (1519165737/500000000000) }

theorem tilt_014_004_valid : tilt_014_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_014_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_014_004]
  · intro i; fin_cases i <;> norm_num [tilt_014_004]
  · norm_num [tilt_014_004]
  · norm_num [tilt_014_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_014_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_014_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_014_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_014_004]

def tilt_014_005 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/40), (-1/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(15738641/100000000), (15738641/100000000), (806701/10000000), (13093241/100000000), (13093241/100000000), (601317/4000000), (9618151/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(140377/20000000), 0, (4190577/100000000), 0, 0]] i.1) i.2
    mu := ![(6280257/100000000), (1/100000000), (569823/12500000), (388423/10000000), (1/100000000), (503733/10000000), (60743/100000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-159881584497823118673382049761872039931253/9644514711874487028982382700000000000000000), (-236169793149947803363/101802230850000000000), (-295234758544847151517629538364446278024931253/4822257355937243514491191350000000000000000), (-236169793149947803363/101802230850000000000), (-590309635505196479916585694679130684009931253/9644514711874487028982382700000000000000000)]
    bernstein := [(26068368290218283492105369999580785973480793049/8229985887466228931398299904000000000000000000000), (90239258197272286963097226337313256791868231449/16459971774932457862796599808000000000000000000000), (1837347945822859943289764024493700375156387983841/296279491948784241530338796544000000000000000000000), (350696667728932360388268110242775896474002866649/65839887099729831451186399232000000000000000000000), (1129033258283653847356681832584534308733227150347/395039322598378988707118395392000000000000000000000)]
    reserve := (2858027527/1000000000000) }

theorem tilt_014_005_valid : tilt_014_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_014_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_014_005]
  · intro i; fin_cases i <;> norm_num [tilt_014_005]
  · norm_num [tilt_014_005]
  · norm_num [tilt_014_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_014_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_014_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_014_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_014_005]

def tilt_014_006 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/40), (-1/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(15738641/100000000), (15738641/100000000), (806701/10000000), (13093241/100000000), (13093241/100000000), (601317/4000000), (9618151/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(740331/100000000), 0, (837827/20000000), 0, 0]] i.1) i.2
    mu := ![(6280257/100000000), (1/100000000), (569823/12500000), (3887701/100000000), (1/100000000), (503733/10000000), (7593/12500000)]
    alternative := (.spike 1 false true)
    polynomial := [(-16130154183028166651884074147995996733443/985440234916222514029819558500000000000000), (-3936166585367420831/1696731780000000000), (-7541319423348165735420255918888837756228517/123180029364527814253727444812500000000000), (-3936166585367420831/1696731780000000000), (-20104808410867432572236721092320902017698231/328480078305407504676606519500000000000000)]
    bernstein := [(8517876219022680458388802818771321931550807707/2522727001385529635916338069760000000000000000000), (28714721170117646624230837854724979457209968907/5045454002771059271832676139520000000000000000000), (194053916357031325182392985619652637139102641521/30272724016626355630996056837120000000000000000000), (3019233570141314514598783624402658365367823311/545454486786060461819748771840000000000000000000), (1115194138916645920770678594176099171674842837/363636324524040307879832514560000000000000000000)]
    reserve := (3066784211/1000000000000) }

theorem tilt_014_006_valid : tilt_014_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_014_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_014_006]
  · intro i; fin_cases i <;> norm_num [tilt_014_006]
  · norm_num [tilt_014_006]
  · norm_num [tilt_014_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_014_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_014_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_014_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_014_006]

def tilt_014_007 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/40), (-1/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(15738641/100000000), (15738641/100000000), (806701/10000000), (13093241/100000000), (13093241/100000000), (601317/4000000), (9618151/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(140377/20000000), 0, (4190577/100000000), 0, 0]] i.1) i.2
    mu := ![(6280257/100000000), (1/100000000), (569601/12500000), (1942983/50000000), (1/100000000), (503733/10000000), (60743/100000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-255579607899809201327090335279611931439/15422940057272957461096713281250000000000), (-211217606140162035533/91050719850000000000), (-7553985558545920229184482414138711806293649/123383520458183659688773706250000000000000), (-211217606140162035533/91050719850000000000), (-132490191608468802729366064762394296681441/2164623165933046661206556250000000000000)]
    bernstein := [(111277192869051309854143071746074931337066607/35095756930327796533695632000000000000000000000), (3465581922776084980843147325282352614849210263/631723624745900337606521376000000000000000000000), (23520375328575934471922139335459174554347383989/3790341748475402025639128256000000000000000000000), (13470415185545186119202697347433573489962632663/2526894498983601350426085504000000000000000000000), (14467472670523661224473002307704228572648284263/5053788997967202700852171008000000000000000000000)]
    reserve := (14313491/5000000000) }

theorem tilt_014_007_valid : tilt_014_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_014_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_014_007]
  · intro i; fin_cases i <;> norm_num [tilt_014_007]
  · norm_num [tilt_014_007]
  · norm_num [tilt_014_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_014_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_014_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_014_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_014_007]

def tilt_014_008 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/40), (-1/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(15738641/100000000), (15738641/100000000), (806701/10000000), (13093241/100000000), (13093241/100000000), (601317/4000000), (9618151/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(740331/100000000), 0, (837827/20000000), 0, 0]] i.1) i.2
    mu := ![(6280257/100000000), (1/100000000), (114009/2500000), (1942983/50000000), (1/100000000), (503733/10000000), (7593/12500000)]
    alternative := (.spike 1 true true)
    polynomial := [(-15366866450402108417363797617731926545199/938461147028765577327165300000000000000000), (-637562204506351121/274815980000000000), (-28727077474449380389678597804362864514545199/469230573514382788663582650000000000000000), (-637562204506351121/274815980000000000), (-57438788082448358670939831811107997102545199/938461147028765577327165300000000000000000)]
    bernstein := [(8104158541823401573160431181865016758043378001/2402460536393639877957543168000000000000000000000), (9109560045221294737923266383653570429470539867/1601640357595759918638362112000000000000000000000), (184689250367392617186496463824644200125938945203/28829526436723678535490518016000000000000000000000), (35434424767347584961754207698279826007679341467/6406561430383039674553448448000000000000000000000), (117705980361188522901525008250653608280167867601/38439368582298238047320690688000000000000000000000)]
    reserve := (3062120547/1000000000000) }

theorem tilt_014_008_valid : tilt_014_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_014_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_014_008]
  · intro i; fin_cases i <;> norm_num [tilt_014_008]
  · norm_num [tilt_014_008]
  · norm_num [tilt_014_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_014_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_014_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_014_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_014_008]

def tilt_014_009 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/40), (-1/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(15738641/100000000), (15738641/100000000), (806701/10000000), (13093241/100000000), (13093241/100000000), (601317/4000000), (9618151/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(140377/20000000), 0, (4190577/100000000), 0, 0]] i.1) i.2
    mu := ![(6280257/100000000), (1/100000000), (569823/12500000), (3884231/100000000), (1/100000000), (503733/10000000), (60743/100000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-78342320073620126573133229660106384761369537/4725813425484918711627509693100000000000000000), (-236169793149947803363/101802230850000000000), (-144665069254673674648637706207879221427466369537/2362906712742459355813754846550000000000000000), (-236169793149947803363/101802230850000000000), (-289251796189273729170702279186098336470171369537/4725813425484918711627509693100000000000000000)]
    bernstein := [(12773227351873523035073915818477806947420050464021/4032694123080463967255474938112000000000000000000000), (44216695275314074402679172658411147711505375137621/8065388246160927934510949876224000000000000000000000), (900290780573287508813707203762434942173180062881789/145176988430896702821197097772032000000000000000000000), (171839201962947757444789047120740692604491274438421/32261552984643711738043799504896000000000000000000000), (553213184268478871409761414439646433614233503036863/193569317907862270428262797029376000000000000000000000)]
    reserve := (2857959051/1000000000000) }

theorem tilt_014_009_valid : tilt_014_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_014_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_014_009]
  · intro i; fin_cases i <;> norm_num [tilt_014_009]
  · norm_num [tilt_014_009]
  · norm_num [tilt_014_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_014_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_014_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_014_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_014_009]

def tilt_014_010 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/40), (-1/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(15738641/100000000), (15738641/100000000), (806701/10000000), (13093241/100000000), (13093241/100000000), (601317/4000000), (9618151/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(740331/100000000), 0, (837827/20000000), 0, 0]] i.1) i.2
    mu := ![(6280257/100000000), (1/100000000), (569823/12500000), (1943851/50000000), (1/100000000), (503733/10000000), (7593/12500000)]
    alternative := (.spike 2 false true)
    polynomial := [(-5603029691210137834033817455513318271933/343359055189047464685374100000000000000000), (-3936166585367420831/1696731780000000000), (-10510535187954762624574776612250278430396933/171679527594523732342687050000000000000000), (-3936166585367420831/1696731780000000000), (-7005155782072771703771839802348347847507311/114453018396349154895124700000000000000000)]
    bernstein := [(3012077464889206477466421974792726930838812467/878999181283961509594557696000000000000000000000), (10093455468350166096426765301365874338005239667/1757998362567923019189115392000000000000000000000), (68144425869880032866923944518101330138434467801/10547990175407538115134692352000000000000000000000), (39277055884165477280893827781386838399109081267/7031993450271692076756461568000000000000000000000), (14612453398638449480947162877967122988200351889/4687995633514461384504307712000000000000000000000)]
    reserve := (623398763/200000000000) }

theorem tilt_014_010_valid : tilt_014_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_014_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_014_010]
  · intro i; fin_cases i <;> norm_num [tilt_014_010]
  · norm_num [tilt_014_010]
  · norm_num [tilt_014_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_014_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_014_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_014_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_014_010]

def tilt_014_011 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/40), (-1/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(15738641/100000000), (15738641/100000000), (806701/10000000), (13093241/100000000), (13093241/100000000), (601317/4000000), (9618151/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(13093/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(140377/20000000), 0, (4190577/100000000), 0, 0]] i.1) i.2
    mu := ![(6280257/100000000), (1/100000000), (569823/12500000), (1942983/50000000), (1/100000000), (503733/10000000), (60743/100000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-1865449178076052830054226087265378440375411/112569627183898468952004162300000000000000000), (-236169793149947803363/101802230850000000000), (-3445944273576007289294873256073835997205375411/56284813591949234476002081150000000000000000), (-236169793149947803363/101802230850000000000), (-6890023097973938525759692286060406615970375411/112569627183898468952004162300000000000000000)]
    bernstein := [(914517083600614359870408751433541717461536149389/288178245590780080517130655488000000000000000000000), (1054405793180555611151217119996232916334607777263/192118830393853387011420436992000000000000000000000), (21465891581202158515795067915816879035450574404967/3458138947089360966205567865856000000000000000000000), (4097863270106564487475936799633960550147862799663/768475321575413548045681747968000000000000000000000), (13205378617565814547126483669095653002065909803789/4610851929452481288274090487808000000000000000000000)]
    reserve := (715994507/250000000000) }

theorem tilt_014_011_valid : tilt_014_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_014_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_014_011]
  · intro i; fin_cases i <;> norm_num [tilt_014_011]
  · norm_num [tilt_014_011]
  · norm_num [tilt_014_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_014_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_014_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_014_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_014_011]

def tilt_014_012 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/40), (-1/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(15738641/100000000), (15738641/100000000), (806701/10000000), (13093241/100000000), (13093241/100000000), (601317/4000000), (9618151/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1939/50000000), 0, 0], ![0, 0, 0, 0, 0], ![(740331/100000000), 0, (837827/20000000), 0, 0]] i.1) i.2
    mu := ![(6280257/100000000), (1/100000000), (569823/12500000), (1942983/50000000), (851/25000000), (503733/10000000), (7593/12500000)]
    alternative := (.spike 2 true true)
    polynomial := [(-131166850470377182072592885474054902771044463/7983194151374888240778745768200000000000000000), (-3936166585367420831/1696731780000000000), (-244373780228661691337642472557105367659670294463/3991597075687444120389372884100000000000000000), (-3936166585367420831/1696731780000000000), (-488616393606853005493212352228736680416569544463/7983194151374888240778745768200000000000000000)]
    bernstein := [(67737985193036317775221223696436043847380262893937/20436977027519713896393589166592000000000000000000000), (25565531076573966785681132544583995383963096274793/4541550450559936421420797592576000000000000000000000), (1556868826134096188394044204831687658428212463176211/245243724330236566756723069999104000000000000000000000), (2687290077021714364790235441997108075906772676789/490978427087560694207653793792000000000000000000000), (26555857477951136689620728653291348084670639374301/8837611687576092495737768288256000000000000000000000)]
    reserve := (375608513/125000000000) }

theorem tilt_014_012_valid : tilt_014_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_014_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_014_012]
  · intro i; fin_cases i <;> norm_num [tilt_014_012]
  · norm_num [tilt_014_012]
  · norm_num [tilt_014_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_014_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_014_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_014_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_014_012]

def tilt_014_013 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/40), (-1/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(15738641/100000000), (15738641/100000000), (806701/10000000), (13093241/100000000), (13093241/100000000), (601317/4000000), (9618151/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(140377/20000000), 0, (4190577/100000000), 0, 0]] i.1) i.2
    mu := ![(6280257/100000000), (1/100000000), (569823/12500000), (1942983/50000000), (1/100000000), (1006967/20000000), (60743/100000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-11151038609057962408580433660610968787612757/675083227284029572721220023100000000000000000), (-236169793149947803363/101802230850000000000), (-20665388828673506529740496890405476142992612757/337541613642014786360610011550000000000000000), (-236169793149947803363/101802230850000000000), (-41319626618737955097072413347150341317197612757/675083227284029572721220023100000000000000000)]
    bernstein := [(5576948822516912896720432975631940810042503644843/1728213061847115706166323259136000000000000000000000), (6384991386791390223022398325675946569815948437881/1152142041231410470777548839424000000000000000000000), (129841690104961837901736992781675915003433406776129/20738556742165388473995879109632000000000000000000000), (24821646438706524693039846184161513379310572186681/4608568164925641883110195357696000000000000000000000), (80672666034346006526586605407901668476320272377643/27651408989553851298661172146176000000000000000000000)]
    reserve := (1458744219/500000000000) }

theorem tilt_014_013_valid : tilt_014_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_014_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_014_013]
  · intro i; fin_cases i <;> norm_num [tilt_014_013]
  · norm_num [tilt_014_013]
  · norm_num [tilt_014_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_014_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_014_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_014_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_014_013]

def tilt_014_014 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/40), (-1/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(15738641/100000000), (15738641/100000000), (806701/10000000), (13093241/100000000), (13093241/100000000), (601317/4000000), (9618151/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(740331/100000000), 0, (837827/20000000), 0, 0]] i.1) i.2
    mu := ![(6280257/100000000), (1/100000000), (569823/12500000), (1942983/50000000), (1/100000000), (201593/4000000), (7593/12500000)]
    alternative := (.spike 3 false true)
    polynomial := [(-1844575748869386983694928174212009240961/112627237283208629830786266000000000000000), (-3936166585367420831/1696731780000000000), (-3447629589868683866968989495851545579643461/56313618641604314915393133000000000000000), (-3936166585367420831/1696731780000000000), (-6893414603988498346954284063528879150045961/112627237283208629830786266000000000000000)]
    bernstein := [(970854389472339036676804271847127480358718839/288325727445014092366812840960000000000000000000), (364057207194653746265962974291396278475113471/64072383876669798303736186880000000000000000000), (22146714826941397661095285871781520125769953317/3459908729340169108401754091520000000000000000000), (1416263002449419035494140220695693222404494271/256289535506679193214944747520000000000000000000), (14105129586725855106237322878142310642907093239/4613211639120225477869005455360000000000000000000)]
    reserve := (152877547/50000000000) }

theorem tilt_014_014_valid : tilt_014_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_014_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_014_014]
  · intro i; fin_cases i <;> norm_num [tilt_014_014]
  · norm_num [tilt_014_014]
  · norm_num [tilt_014_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_014_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_014_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_014_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_014_014]

def tilt_014_015 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/40), (-1/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(15738641/100000000), (15738641/100000000), (806701/10000000), (13093241/100000000), (13093241/100000000), (601317/4000000), (9618151/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(13093/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(140377/20000000), 0, (4190577/100000000), 0, 0]] i.1) i.2
    mu := ![(6280257/100000000), (1/100000000), (569823/12500000), (1942983/50000000), (1/100000000), (503733/10000000), (60743/100000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-1865449178076052830054226087265378440375411/112569627183898468952004162300000000000000000), (-236169793149947803363/101802230850000000000), (-3445944273576007289294873256073835997205375411/56284813591949234476002081150000000000000000), (-236169793149947803363/101802230850000000000), (-6890023097973938525759692286060406615970375411/112569627183898468952004162300000000000000000)]
    bernstein := [(914517083600614359870408751433541717461536149389/288178245590780080517130655488000000000000000000000), (1054405793180555611151217119996232916334607777263/192118830393853387011420436992000000000000000000000), (21465891581202158515795067915816879035450574404967/3458138947089360966205567865856000000000000000000000), (4097863270106564487475936799633960550147862799663/768475321575413548045681747968000000000000000000000), (13205378617565814547126483669095653002065909803789/4610851929452481288274090487808000000000000000000000)]
    reserve := (715994507/250000000000) }

theorem tilt_014_015_valid : tilt_014_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_014_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_014_015]
  · intro i; fin_cases i <;> norm_num [tilt_014_015]
  · norm_num [tilt_014_015]
  · norm_num [tilt_014_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_014_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_014_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_014_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_014_015]

def tilt_014_016 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/40), (-1/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(15738641/100000000), (15738641/100000000), (806701/10000000), (13093241/100000000), (13093241/100000000), (601317/4000000), (9618151/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1939/50000000), 0, 0], ![0, 0, 0, 0, 0], ![(740331/100000000), 0, (837827/20000000), 0, 0]] i.1) i.2
    mu := ![(6280257/100000000), (1/100000000), (569823/12500000), (1942983/50000000), (851/25000000), (503733/10000000), (7593/12500000)]
    alternative := (.spike 3 true true)
    polynomial := [(-131166850470377182072592885474054902771044463/7983194151374888240778745768200000000000000000), (-3936166585367420831/1696731780000000000), (-244373780228661691337642472557105367659670294463/3991597075687444120389372884100000000000000000), (-3936166585367420831/1696731780000000000), (-488616393606853005493212352228736680416569544463/7983194151374888240778745768200000000000000000)]
    bernstein := [(67737985193036317775221223696436043847380262893937/20436977027519713896393589166592000000000000000000000), (25565531076573966785681132544583995383963096274793/4541550450559936421420797592576000000000000000000000), (1556868826134096188394044204831687658428212463176211/245243724330236566756723069999104000000000000000000000), (2687290077021714364790235441997108075906772676789/490978427087560694207653793792000000000000000000000), (26555857477951136689620728653291348084670639374301/8837611687576092495737768288256000000000000000000000)]
    reserve := (375608513/125000000000) }

theorem tilt_014_016_valid : tilt_014_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_014_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_014_016]
  · intro i; fin_cases i <;> norm_num [tilt_014_016]
  · norm_num [tilt_014_016]
  · norm_num [tilt_014_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_014_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_014_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_014_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_014_016]

def tilt_014_017 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/40), (-1/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(15738641/100000000), (15738641/100000000), (806701/10000000), (13093241/100000000), (13093241/100000000), (601317/4000000), (9618151/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(140377/20000000), 0, (4190577/100000000), 0, 0]] i.1) i.2
    mu := ![(6280257/100000000), (1/100000000), (569823/12500000), (1942983/50000000), (1/100000000), (1258709/25000000), (60743/100000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-5575529555655417184110387821415028916991263/337541680683261151338764481480000000000000000), (-236169793149947803363/101802230850000000000), (-10332696475721411392002665208923942717930991263/168770840341630575669382240740000000000000000), (-236169793149947803363/101802230850000000000), (-20659817421887167366821220030026470406944991263/337541680683261151338764481480000000000000000)]
    bernstein := [(2788451527857011411054215100178943840861625687137/864106702549148547427237072588800000000000000000000), (3192480707531729573802816464756757602243850128779/576071135032765698284824715059200000000000000000000), (64920576860974184212645164257224363135684339395811/10369280430589782569126844871065600000000000000000000), (12410763233831584284857654783639187523454693547979/2304284540131062793139298860236800000000000000000000), (40335966384076518476258518543301197368654586362337/13825707240786376758835793161420800000000000000000000)]
    reserve := (145873067/50000000000) }

theorem tilt_014_017_valid : tilt_014_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_014_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_014_017]
  · intro i; fin_cases i <;> norm_num [tilt_014_017]
  · norm_num [tilt_014_017]
  · norm_num [tilt_014_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_014_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_014_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_014_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_014_017]

def tilt_014_018 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/40), (-1/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(15738641/100000000), (15738641/100000000), (806701/10000000), (13093241/100000000), (13093241/100000000), (601317/4000000), (9618151/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(740331/100000000), 0, (837827/20000000), 0, 0]] i.1) i.2
    mu := ![(6280257/100000000), (1/100000000), (569823/12500000), (1942983/50000000), (1/100000000), (201593/4000000), (7593/12500000)]
    alternative := (.spike 4 false true)
    polynomial := [(-9211970921649202708504120328886488972669/563136186416043149153931330000000000000000), (-3936166585367420831/1696731780000000000), (-17238137041520721602634976958715554340985169/281568093208021574576965665000000000000000), (-3936166585367420831/1696731780000000000), (-34467062112119794002561449797102222192997669/563136186416043149153931330000000000000000)]
    bernstein := [(4882230889408345081712669583455441472761821531/1441628637225070461834064204800000000000000000000), (1826497193825397701039718609796046756465323459/320361919383348991518680934400000000000000000000), (111068889363416902718934837153318115311167811793/17299543646700845542008770457600000000000000000000), (7106148005008792576042277511416228382814806659/1281447677533395966074723737600000000000000000000), (70972571982366740521598968431600821148954599131/23066058195601127389345027276800000000000000000000)]
    reserve := (3076926771/1000000000000) }

theorem tilt_014_018_valid : tilt_014_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_014_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_014_018]
  · intro i; fin_cases i <;> norm_num [tilt_014_018]
  · norm_num [tilt_014_018]
  · norm_num [tilt_014_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_014_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_014_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_014_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_014_018]

def tilt_014_019 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/40), (-1/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(15738641/100000000), (15738641/100000000), (806701/10000000), (13093241/100000000), (13093241/100000000), (601317/4000000), (9618151/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(358459/50000000), 0, (4190577/100000000), 0, 0]] i.1) i.2
    mu := ![(6280257/100000000), (1/100000000), (569823/12500000), (1942983/50000000), (1/100000000), (503733/10000000), (60743/100000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-1863499838267077109620411696605808672490911/112569627183898468952004162300000000000000000), (-6214995192875212001/2679006075000000000), (-3445942324222829962419551961935931628214165911/56284813591949234476002081150000000000000000), (-6214995192875212001/2679006075000000000), (-6890021148607392847729483512175257447755840911/112569627183898468952004162300000000000000000)]
    bernstein := [(919515345609542113848437968651103976651941083889/288178245590780080517130655488000000000000000000000), (1057736784685244682346188272787009342676994488763/192118830393853387011420436992000000000000000000000), (21525831257681217529698781076285761618181215608467/3458138947089360966205567865856000000000000000000000), (4111179854321231130088243051131137469155824711163/768475321575413548045681747968000000000000000000000), (13285262221142015175338921822484264327402725938289/4610851929452481288274090487808000000000000000000000)]
    reserve := (2881303157/1000000000000) }

theorem tilt_014_019_valid : tilt_014_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_014_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_014_019]
  · intro i; fin_cases i <;> norm_num [tilt_014_019]
  · norm_num [tilt_014_019]
  · norm_num [tilt_014_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_014_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_014_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_014_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_014_019]

def tilt_014_020 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/40), (-1/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(15738641/100000000), (15738641/100000000), (806701/10000000), (13093241/100000000), (13093241/100000000), (601317/4000000), (9618151/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(362649/50000000), 0, (837827/20000000), 0, 0]] i.1) i.2
    mu := ![(6280257/100000000), (1/100000000), (569823/12500000), (1942983/50000000), (1/100000000), (503733/10000000), (7593/12500000)]
    alternative := (.spike 4 true true)
    polynomial := [(-61246609761371003656323277519294430422511/3752382679847186012116919280000000000000000), (-15744664729515666479/6786927120000000000), (-114863885094952099677139649199754720554345011/1876191339923593006058459640000000000000000), (-15744664729515666479/6786927120000000000), (-229666523580142828350622975121990146678267511/3752382679847186012116919280000000000000000)]
    bernstein := [(32880955787554323948256275821183943557829537289/9606099660408796191019313356800000000000000000000), (12248122324373003138710707908509500106806595521/2134688813424176931337625190400000000000000000000), (744276824149665813185145538087694867058231048667/115273195924905554292231760281600000000000000000000), (47660744486216203356882833484035071585183816321/8538755253696707725350500761600000000000000000000), (478493280105215714162632547685637161355735031689/153697594566540739056309013708800000000000000000000)]
    reserve := (778303137/250000000000) }

theorem tilt_014_020_valid : tilt_014_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_014_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_014_020]
  · intro i; fin_cases i <;> norm_num [tilt_014_020]
  · norm_num [tilt_014_020]
  · norm_num [tilt_014_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_014_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_014_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_014_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_014_020]

def tiltBundle014_row : Alternative → Row
  | .zero => tilt_014_000
  | (.spike 0 false false) => tilt_014_001
  | (.spike 0 false true) => tilt_014_002
  | (.spike 0 true false) => tilt_014_003
  | (.spike 0 true true) => tilt_014_004
  | (.spike 1 false false) => tilt_014_005
  | (.spike 1 false true) => tilt_014_006
  | (.spike 1 true false) => tilt_014_007
  | (.spike 1 true true) => tilt_014_008
  | (.spike 2 false false) => tilt_014_009
  | (.spike 2 false true) => tilt_014_010
  | (.spike 2 true false) => tilt_014_011
  | (.spike 2 true true) => tilt_014_012
  | (.spike 3 false false) => tilt_014_013
  | (.spike 3 false true) => tilt_014_014
  | (.spike 3 true false) => tilt_014_015
  | (.spike 3 true true) => tilt_014_016
  | (.spike 4 false false) => tilt_014_017
  | (.spike 4 false true) => tilt_014_018
  | (.spike 4 true false) => tilt_014_019
  | (.spike 4 true true) => tilt_014_020

def tiltBundle014 : TiltBundle where
  interval := ⟨(-1/40), (-1/80)⟩
  lambda := ![(15738641/100000000), (15738641/100000000), (806701/10000000), (13093241/100000000), (13093241/100000000), (601317/4000000), (9618151/50000000)]
  row := tiltBundle014_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_014_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_014_001_valid | exact tilt_014_002_valid | exact tilt_014_003_valid | exact tilt_014_004_valid | exact tilt_014_005_valid | exact tilt_014_006_valid | exact tilt_014_007_valid | exact tilt_014_008_valid | exact tilt_014_009_valid | exact tilt_014_010_valid | exact tilt_014_011_valid | exact tilt_014_012_valid | exact tilt_014_013_valid | exact tilt_014_014_valid | exact tilt_014_015_valid | exact tilt_014_016_valid | exact tilt_014_017_valid | exact tilt_014_018_valid | exact tilt_014_019_valid | exact tilt_014_020_valid
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
