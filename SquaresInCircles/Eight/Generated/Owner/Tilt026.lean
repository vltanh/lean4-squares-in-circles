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

def tilt_026_000 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/64), (3/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14570673/100000000), (14570673/100000000), (8773791/100000000), (14541661/100000000), (14541661/100000000), (16571599/100000000), (16429943/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2774467/50000000), (1/100000000), (2118977/50000000), (4291427/100000000), (1/100000000), (2785463/50000000), (160371/100000000)]
    alternative := .zero
    polynomial := [(-440579777614888082731693428291288045716752081/80501269877884854213492584881350000000000000000), (267098724944587/423795400000000), (-695526721125714714833950881644751326783466752081/40250634938942427106746292440675000000000000000), (267098724944587/423795400000000), (-154512540274868282398352229984579040613468528009/8944585541987206023721398320150000000000000000)]
    bernstein := [(212601287112318212978240095321183038712318668813871/1350587193015567822268275210952743321600000000000000000), (256704026030578228167415988628958625551140718465583/1125489327512973185223562675793952768000000000000000000), (6853362385780628272396300401756228514701368423996149/25323509869041896667530160205363937280000000000000000000), (859375322462912620209423775319508389802844742060579/3014703555838321031848828595876659200000000000000000000), (14316422939750612983225054321729394367860618279996639/52757312227170618057354500427841536000000000000000000000)]
    reserve := (78706983/500000000000) }

theorem tilt_026_000_valid : tilt_026_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_026_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_026_000]
  · intro i; fin_cases i <;> norm_num [tilt_026_000]
  · norm_num [tilt_026_000]
  · norm_num [tilt_026_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_026_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_026_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_026_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_026_000]

def tilt_026_001 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/64), (3/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14570673/100000000), (14570673/100000000), (8773791/100000000), (14541661/100000000), (14541661/100000000), (16571599/100000000), (16429943/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(14571/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2774467/50000000), (1/100000000), (2118977/50000000), (4291427/100000000), (1/100000000), (2785463/50000000), (164437/100000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-62571496860231942216020270794872927976416769/11791753688019611465471652053350000000000000000), (436398402944631816739/711098410100000000000), (-99405013110880326771462209884035681029816916769/5895876844009805732735826026675000000000000000), (436398402944631816739/711098410100000000000), (-2184037964009894742864927467003038342106125459/129579710857358367752435736850000000000000000)]
    bernstein := [(2552490607938571476137300099661930295713405605883/15217907587900125676330342182761267200000000000000000), (16653743276002927698040508433758648055502736562843/70654570943822012068676588705677312000000000000000000), (1024707341589321825735055280183789787186750012830501/3709364974550655633605520907048058880000000000000000000), (894428833412820884564131015068594571244492127720997/3091137478792213028004600755873382400000000000000000000), (2125260188953240757843518837023439338820458850246511/7727843696980532570011501889683456000000000000000000000)]
    reserve := (83864703/500000000000) }

theorem tilt_026_001_valid : tilt_026_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_026_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_026_001]
  · intro i; fin_cases i <;> norm_num [tilt_026_001]
  · norm_num [tilt_026_001]
  · norm_num [tilt_026_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_026_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_026_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_026_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_026_001]

def tilt_026_002 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/64), (3/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14570673/100000000), (14570673/100000000), (8773791/100000000), (14541661/100000000), (14541661/100000000), (16571599/100000000), (16429943/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (1079/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2774467/50000000), (947/25000000), (2118977/50000000), (4291427/100000000), (1/100000000), (2785463/50000000), (15631/10000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-23866748075517280960856252986032837387781628531/4245956958515918335544863051597400000000000000000), (278597865202776158757/430152331000000000000), (-37621186022886008803260284750739653432359199628531/2122978479257959167772431525798700000000000000000), (278597865202776158757/430152331000000000000), (-2593741561989534493984817698223906000942435090639/146412308914342011570512519020600000000000000000)]
    bernstein := [(12383776614160144146231229263217081196817080551495821/71235337019724601353796645107068724838400000000000000000), (44051310482922439568818085152638429923701829008293799/178088342549311503384491612767671812096000000000000000000), (130019779039445158592967731820731356222196307529407733/445220856373278758461229031919179530240000000000000000000), (342678878503833831952428668336094748248212985370567903/1113052140933196896153072579797948825600000000000000000000), (820508001094585608595699321546928229300838717164844189/2782630352332992240382681449494872064000000000000000000000)]
    reserve := (173843167/1000000000000) }

theorem tilt_026_002_valid : tilt_026_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_026_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_026_002]
  · intro i; fin_cases i <;> norm_num [tilt_026_002]
  · norm_num [tilt_026_002]
  · norm_num [tilt_026_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_026_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_026_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_026_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_026_002]

def tilt_026_003 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/64), (3/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14570673/100000000), (14570673/100000000), (8773791/100000000), (14541661/100000000), (14541661/100000000), (16571599/100000000), (16429943/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(277309/5000000), (1/100000000), (2118977/50000000), (4291427/100000000), (1/100000000), (2785463/50000000), (164437/100000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-24743599219547221098978306921477641720395441/4714360521817027105932027101800000000000000000), (436398402944631816739/711098410100000000000), (-39741998324602546517184938738900946496694395441/2357180260908513552966013550900000000000000000), (436398402944631816739/711098410100000000000), (-873178604944896107838141749130554014853498851/51806159580406891273978319800000000000000000)]
    bernstein := [(1372437628473232804908462606334033891563318544587/6084141905876690479544346154211737600000000000000000), (8292315731598113361200793630292374927530097234027/28247801705856062940741607144554496000000000000000000), (495475515598299783614713843208361908831382950101589/1483009589557443304388934375089111040000000000000000000), (429094596470910318489487385657951173014796438107733/1235841324631202753657445312574259200000000000000000000), (1028444202892151327397106033017702134964637866996479/3089603311578006884143613281435648000000000000000000000)]
    reserve := (112788101/500000000000) }

theorem tilt_026_003_valid : tilt_026_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_026_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_026_003]
  · intro i; fin_cases i <;> norm_num [tilt_026_003]
  · norm_num [tilt_026_003]
  · norm_num [tilt_026_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_026_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_026_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_026_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_026_003]

def tilt_026_004 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/64), (3/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14570673/100000000), (14570673/100000000), (8773791/100000000), (14541661/100000000), (14541661/100000000), (16571599/100000000), (16429943/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5551689/100000000), (1/100000000), (2118977/50000000), (4291427/100000000), (1/100000000), (2785463/50000000), (15631/10000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-2267675060965959574940352041965229932396411/407801194312487287988309333700000000000000000), (278597865202776158757/430152331000000000000), (-3613286781711228412662436379668825953091396411/203900597156243643994154666850000000000000000), (278597865202776158757/430152331000000000000), (-249113996150396236749997669217092644008634359/14062110148706458206493425300000000000000000)]
    bernstein := [(1602264902429155511401260845234690595601816432901/6841768722038570727834071166300979200000000000000000), (5263115825504396984792190911708101072802964834319/17104421805096426819585177915752448000000000000000000), (3477321960589295359241763090978345918114323867363/9867935656786400088222218028318720000000000000000000), (39364556296458342035602648215621624073432833310343/106902636281852667622407361973452800000000000000000000), (94936559192590826271461050716235788719822786741909/267256590704631669056018404933632000000000000000000000)]
    reserve := (234188697/1000000000000) }

theorem tilt_026_004_valid : tilt_026_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_026_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_026_004]
  · intro i; fin_cases i <;> norm_num [tilt_026_004]
  · norm_num [tilt_026_004]
  · norm_num [tilt_026_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_026_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_026_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_026_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_026_004]

def tilt_026_005 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/64), (3/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14570673/100000000), (14570673/100000000), (8773791/100000000), (14541661/100000000), (14541661/100000000), (16571599/100000000), (16429943/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2774467/50000000), (1/100000000), (2118977/50000000), (4289529/100000000), (1/100000000), (2785463/50000000), (164437/100000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-12530481536318392313377813349200273149192901/2357307693017594191856142498090000000000000000), (436398402944631816739/711098410100000000000), (-139105619984988702429171873119488541185715250307/8250576925561579671496498743315000000000000000), (436398402944631816739/711098410100000000000), (-21394117430709475085550007811194821573798934639/1269319527009473795614845960510000000000000000)]
    bernstein := [(3375622108454048553675409446140768970242934517649/21295647877655775915370123486203740160000000000000000), (156754951298513169894999733055000890785838800519703/692108556023812717249529013301621555200000000000000000), (1386106673728419733959827958560038457543364779991503/5190814170178595379371467599762161664000000000000000000), (1211770076204162306366859187093676026114224342262991/4325678475148829482809556333135134720000000000000000000), (2874351311923715524996424836124129377471089808839533/10814196187872073707023890832837836800000000000000000000)]
    reserve := (158512299/1000000000000) }

theorem tilt_026_005_valid : tilt_026_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_026_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_026_005]
  · intro i; fin_cases i <;> norm_num [tilt_026_005]
  · norm_num [tilt_026_005]
  · norm_num [tilt_026_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_026_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_026_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_026_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_026_005]

def tilt_026_006 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/64), (3/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14570673/100000000), (14570673/100000000), (8773791/100000000), (14541661/100000000), (14541661/100000000), (16571599/100000000), (16429943/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2774467/50000000), (1/100000000), (2118977/50000000), (2146663/50000000), (1/100000000), (2785463/50000000), (15631/10000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-435787792745959845583269003654536970238451/78497494358309640190614511243000000000000000), (278597865202776158757/430152331000000000000), (-695519460683665651386050326864461579379248451/39248747179154820095307255621500000000000000), (278597865202776158757/430152331000000000000), (-47951832192227080790569564990526504199595119/2706810150286539316917741767000000000000000)]
    bernstein := [(320439446090847819207776537647758308791058866541/1316969418308142228360220827858239488000000000000000), (1043146833987158566857014972269649007410532841479/3292423545770355570900552069645598720000000000000000), (8926928191685335260495210253582481058037971770879/24693176593277666781754140522341990400000000000000000), (7765111543079549369106996337738497242885261948863/20577647161064722318128450435284992000000000000000000), (18743937383306622014055567065254917900096676204669/51444117902661805795321126088212480000000000000000000)]
    reserve := (243315783/1000000000000) }

theorem tilt_026_006_valid : tilt_026_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_026_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_026_006]
  · intro i; fin_cases i <;> norm_num [tilt_026_006]
  · norm_num [tilt_026_006]
  · norm_num [tilt_026_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_026_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_026_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_026_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_026_006]

def tilt_026_007 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/64), (3/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14570673/100000000), (14570673/100000000), (8773791/100000000), (14541661/100000000), (14541661/100000000), (16571599/100000000), (16429943/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2774467/50000000), (1/100000000), (4236029/100000000), (4291427/100000000), (1/100000000), (2785463/50000000), (164437/100000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-62651241235337222085644620741203843227630069/11786397536006296136406958823975000000000000000), (6108166585796867320021/9950855723900000000000), (-99361747196285799211525062293692242698143505069/5893198768003148068203479411987500000000000000), (6108166585796867320021/9950855723900000000000), (-15281603319333558553920344612818713965619952313/906645964308176625877458371075000000000000000)]
    bernstein := [(349019468584302293234892980135115216398211685569/2172999311246652831213901231790489600000000000000000), (113056032604382424575667175524877685523148728395601/494357343308613519101162530232336384000000000000000000), (998604233230883966912039627399669001474213099706201/3707680074814601393258718976742522880000000000000000000), (872961665799489824871850407063233675998381750343897/3089733395678834494382265813952102400000000000000000000), (2072398221846791181797473497837289300757334114579211/7724333489197086235955664534880256000000000000000000000)]
    reserve := (32123293/200000000000) }

theorem tilt_026_007_valid : tilt_026_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_026_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_026_007]
  · intro i; fin_cases i <;> norm_num [tilt_026_007]
  · norm_num [tilt_026_007]
  · norm_num [tilt_026_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_026_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_026_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_026_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_026_007]

def tilt_026_008 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/64), (3/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14570673/100000000), (14570673/100000000), (8773791/100000000), (14541661/100000000), (14541661/100000000), (16571599/100000000), (16429943/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2774467/50000000), (1/100000000), (4239879/100000000), (4291427/100000000), (1/100000000), (2785463/50000000), (15631/10000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-8300870454991025823769641572703002806790407/1495207882326197297245734338900000000000000000), (185776981795247846313/286898479000000000000), (-13247919542057199296955636333830001338623290407/747603941163098648622867169450000000000000000), (185776981795247846313/286898479000000000000), (-913363386677910605796120794003010333601372083/51558892494006803353301184100000000000000000)]
    bernstein := [(6050936108686130488564658410864408045046166628537/25085425606689194514507890082342502400000000000000000), (19731583129415949525345965810087862485374671522603/62713564016722986286269725205856256000000000000000000), (168956196447026796927464790520851171189984168534403/470351730125422397147022939043921920000000000000000000), (146967809597660296621603667912054652132196195484291/391959775104518664289185782536601600000000000000000000), (354583238760574524034319686097068217067231281911433/979899437761296660722964456341504000000000000000000000)]
    reserve := (60303303/250000000000) }

theorem tilt_026_008_valid : tilt_026_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_026_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_026_008]
  · intro i; fin_cases i <;> norm_num [tilt_026_008]
  · norm_num [tilt_026_008]
  · norm_num [tilt_026_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_026_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_026_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_026_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_026_008]

def tilt_026_009 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/64), (3/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14570673/100000000), (14570673/100000000), (8773791/100000000), (14541661/100000000), (14541661/100000000), (16571599/100000000), (16429943/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2774467/50000000), (1/100000000), (2118977/50000000), (428953/10000000), (1/100000000), (2785463/50000000), (164437/100000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-12530669216683523154286138091177722396435339/2357308242566902057030662091300000000000000000), (436398402944631816739/711098410100000000000), (-19872236243916549902001993799514049115855435339/1178654121283451028515331045650000000000000000), (436398402944631816739/711098410100000000000), (-3056303216816647406219207804687455423793418103/181331403274377081310050930100000000000000000)]
    bernstein := [(481993283853077757689389112693710452199777140873/3042236120317331558588287425288601600000000000000000), (22385816166986075380948248921500361789803712286431/98872673910313275654119341321879552000000000000000000), (197957130802987979673818042680697696192118222595031/741545054327349567405895059914096640000000000000000000), (173061586508703383421074462060513298830640032552407/617954211939457972838245883261747200000000000000000000), (410500542783309087244624182794068250202423399486341/1544885529848644932095614708154368000000000000000000000)]
    reserve := (158433883/1000000000000) }

theorem tilt_026_009_valid : tilt_026_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_026_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_026_009]
  · intro i; fin_cases i <;> norm_num [tilt_026_009]
  · norm_num [tilt_026_009]
  · norm_num [tilt_026_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_026_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_026_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_026_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_026_009]

def tilt_026_010 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/64), (3/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14570673/100000000), (14570673/100000000), (8773791/100000000), (14541661/100000000), (14541661/100000000), (16571599/100000000), (16429943/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2774467/50000000), (1/100000000), (2118977/50000000), (4293327/100000000), (1/100000000), (2785463/50000000), (15631/10000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-86253281348165429899067001012527741885908811/15699502528383749689199023214700000000000000000), (278597865202776158757/430152331000000000000), (-139103020239261613722544853140912694510714908811/7849751264191874844599511607350000000000000000), (278597865202776158757/430152331000000000000), (-9590337489557760759144504802786650388949789959/541362156151163782386173214300000000000000000)]
    bernstein := [(79266907569795100817870070809974868085735471861301/263393945011240299425624879462036275200000000000000000), (246578776405485260016465017403971243893439247253919/658484862528100748564062198655090688000000000000000000), (2070021081874381174902528433266365983297344028455319/4938636468960755614230466489913180160000000000000000000), (1790231649162016631072321157958199790000683251771543/4115530390800629678525388741594316800000000000000000000), (4341845534101409426331244161071027516727113274317509/10288825977001574196313471853985792000000000000000000000)]
    reserve := (18809019/62500000000) }

theorem tilt_026_010_valid : tilt_026_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_026_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_026_010]
  · intro i; fin_cases i <;> norm_num [tilt_026_010]
  · norm_num [tilt_026_010]
  · norm_num [tilt_026_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_026_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_026_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_026_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_026_010]

def tilt_026_011 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/64), (3/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14570673/100000000), (14570673/100000000), (8773791/100000000), (14541661/100000000), (14541661/100000000), (16571599/100000000), (16429943/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7271/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2774467/50000000), (1/100000000), (2118977/50000000), (4291427/100000000), (1/100000000), (2785463/50000000), (164437/100000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-187725605015344501191762530657049890382049307/35375261064058834396414956160050000000000000000), (436398402944631816739/711098410100000000000), (-298215050447075628988930331370379474195903549307/17687630532029417198207478080025000000000000000), (436398402944631816739/711098410100000000000), (-6552114014166328719523834068242878005510165377/388739132572075103257307210550000000000000000)]
    bernstein := [(7643121029094039541956383744714287338465569910649/45653722763700377028991026548283801600000000000000000), (49894597885669667148463373732175238387437554941529/211963712831466036206029766117031936000000000000000000), (3070623665646249650255353427563674570970938967862503/11128094923651966900816562721144176640000000000000000000), (2680371039686952538543133288131900428384796182549991/9273412436376639084013802267620147200000000000000000000), (6368491488536611608797822632430751770781951454820533/23183531090941597710034505669050368000000000000000000000)]
    reserve := (83707533/500000000000) }

theorem tilt_026_011_valid : tilt_026_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_026_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_026_011]
  · intro i; fin_cases i <;> norm_num [tilt_026_011]
  · norm_num [tilt_026_011]
  · norm_num [tilt_026_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_026_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_026_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_026_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_026_011]

def tilt_026_012 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/64), (3/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14570673/100000000), (14570673/100000000), (8773791/100000000), (14541661/100000000), (14541661/100000000), (16571599/100000000), (16429943/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4307/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2774467/50000000), (1/100000000), (2118977/50000000), (4291427/100000000), (3781/100000000), (2785463/50000000), (15631/10000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-47643086693515507136484337353341563289401485753/8476221362274914058445156915570100000000000000000), (278597865202776158757/430152331000000000000), (-75103326390842654074092207225424323331814708485753/4238110681137457029222578457785050000000000000000), (278597865202776158757/430152331000000000000), (-5177896886034199746243032072879148451735862602957/292283495250859105463626100536900000000000000000)]
    bernstein := [(24758725235392651988292529023513026988119126127822023/142207396658700484539971021726413330841600000000000000000), (88032169492544139479590935932803488601870163575390037/355518491646751211349927554316033327104000000000000000000), (779369774328581988120240102708974286110845484985962237/2666388687350634085124456657370249953280000000000000000000), (684668549395177855261528525454681400574991128901025789/2221990572792195070937047214475208294400000000000000000000), (1639426818682881013307000486008243756801255814528591607/5554976431980487677342618036188020736000000000000000000000)]
    reserve := (34820587/200000000000) }

theorem tilt_026_012_valid : tilt_026_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_026_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_026_012]
  · intro i; fin_cases i <;> norm_num [tilt_026_012]
  · norm_num [tilt_026_012]
  · norm_num [tilt_026_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_026_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_026_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_026_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_026_012]

def tilt_026_013 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/64), (3/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14570673/100000000), (14570673/100000000), (8773791/100000000), (14541661/100000000), (14541661/100000000), (16571599/100000000), (16429943/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2774467/50000000), (1/100000000), (2118977/50000000), (4291427/100000000), (1/100000000), (1113633/20000000), (164437/100000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-12370464155750979466335981865644843795577853/2357181918203606361873697889925000000000000000), (436398402944631816739/711098410100000000000), (-19871011789125072105788588669760296621413327853/1178590959101803180936848944962500000000000000), (436398402944631816739/711098410100000000000), (-436589594660377947605613641292911520868473383/25903098002237432548062614175000000000000000)]
    bernstein := [(687954846579543460713168879424167182444609119471/3042073091768941224009938016770457600000000000000000), (4154219084379434613548370063358545575857231342991/14123910783212941397188997935005696000000000000000000), (248161014941101525505501076996658194023216595113137/741505316118679423352422391587799040000000000000000000), (214900037720027212248988264173076000644850164023089/617921096765566186127018659656499200000000000000000000), (515103986220511652555548003481726519826404905951507/1544802741913915465317546649141248000000000000000000000)]
    reserve := (113073359/500000000000) }

theorem tilt_026_013_valid : tilt_026_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_026_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_026_013]
  · intro i; fin_cases i <;> norm_num [tilt_026_013]
  · norm_num [tilt_026_013]
  · norm_num [tilt_026_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_026_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_026_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_026_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_026_013]

def tilt_026_014 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/64), (3/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14570673/100000000), (14570673/100000000), (8773791/100000000), (14541661/100000000), (14541661/100000000), (16571599/100000000), (16429943/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2774467/50000000), (1/100000000), (2118977/50000000), (4291427/100000000), (1/100000000), (5573689/100000000), (15631/10000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-2268024053217612269113432104972875829517031/407800980754003958838674873300000000000000000), (278597865202776158757/430152331000000000000), (-3613285239674776755850240011874153725160517031/203900490377001979419337436650000000000000000), (278597865202776158757/430152331000000000000), (-249113877768839168945909192815287399120397139/14062102784620826166850857700000000000000000)]
    bernstein := [(1596386152282276282809585422903130803066208999321/6841765139121767282291557503126732800000000000000000), (5248417574287047346459312303538046127611977060299/17104412847804418205728893757816832000000000000000000), (15031646620985040892752234894131499951882507163233/42761032119511045514322234394542080000000000000000000), (39272678974126868529272163168840379495353148218403/106902580298777613785805585986355200000000000000000000), (94706854254840237649976697087034905030501335075689/267256450746944034464513964965888000000000000000000000)]
    reserve := (9333183/40000000000) }

theorem tilt_026_014_valid : tilt_026_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_026_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_026_014]
  · intro i; fin_cases i <;> norm_num [tilt_026_014]
  · norm_num [tilt_026_014]
  · norm_num [tilt_026_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_026_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_026_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_026_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_026_014]

def tilt_026_015 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/64), (3/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14570673/100000000), (14570673/100000000), (8773791/100000000), (14541661/100000000), (14541661/100000000), (16571599/100000000), (16429943/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7271/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2774467/50000000), (1/100000000), (2118977/50000000), (4291427/100000000), (1/100000000), (2785463/50000000), (164437/100000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-187725605015344501191762530657049890382049307/35375261064058834396414956160050000000000000000), (436398402944631816739/711098410100000000000), (-298215050447075628988930331370379474195903549307/17687630532029417198207478080025000000000000000), (436398402944631816739/711098410100000000000), (-6552114014166328719523834068242878005510165377/388739132572075103257307210550000000000000000)]
    bernstein := [(7643121029094039541956383744714287338465569910649/45653722763700377028991026548283801600000000000000000), (49894597885669667148463373732175238387437554941529/211963712831466036206029766117031936000000000000000000), (3070623665646249650255353427563674570970938967862503/11128094923651966900816562721144176640000000000000000000), (2680371039686952538543133288131900428384796182549991/9273412436376639084013802267620147200000000000000000000), (6368491488536611608797822632430751770781951454820533/23183531090941597710034505669050368000000000000000000000)]
    reserve := (83707533/500000000000) }

theorem tilt_026_015_valid : tilt_026_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_026_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_026_015]
  · intro i; fin_cases i <;> norm_num [tilt_026_015]
  · norm_num [tilt_026_015]
  · norm_num [tilt_026_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_026_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_026_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_026_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_026_015]

def tilt_026_016 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/64), (3/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14570673/100000000), (14570673/100000000), (8773791/100000000), (14541661/100000000), (14541661/100000000), (16571599/100000000), (16429943/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4307/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2774467/50000000), (1/100000000), (2118977/50000000), (4291427/100000000), (3781/100000000), (2785463/50000000), (15631/10000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-47643086693515507136484337353341563289401485753/8476221362274914058445156915570100000000000000000), (278597865202776158757/430152331000000000000), (-75103326390842654074092207225424323331814708485753/4238110681137457029222578457785050000000000000000), (278597865202776158757/430152331000000000000), (-5177896886034199746243032072879148451735862602957/292283495250859105463626100536900000000000000000)]
    bernstein := [(24758725235392651988292529023513026988119126127822023/142207396658700484539971021726413330841600000000000000000), (88032169492544139479590935932803488601870163575390037/355518491646751211349927554316033327104000000000000000000), (779369774328581988120240102708974286110845484985962237/2666388687350634085124456657370249953280000000000000000000), (684668549395177855261528525454681400574991128901025789/2221990572792195070937047214475208294400000000000000000000), (1639426818682881013307000486008243756801255814528591607/5554976431980487677342618036188020736000000000000000000000)]
    reserve := (34820587/200000000000) }

theorem tilt_026_016_valid : tilt_026_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_026_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_026_016]
  · intro i; fin_cases i <;> norm_num [tilt_026_016]
  · norm_num [tilt_026_016]
  · norm_num [tilt_026_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_026_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_026_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_026_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_026_016]

def tilt_026_017 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/64), (3/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14570673/100000000), (14570673/100000000), (8773791/100000000), (14541661/100000000), (14541661/100000000), (16571599/100000000), (16429943/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2774467/50000000), (1/100000000), (2118977/50000000), (4291427/100000000), (1/100000000), (2784083/50000000), (164437/100000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-123705332193993208343710107015914814869776173/23571823415355152050215503464700000000000000000), (436398402944631816739/711098410100000000000), (-198710154246493632207312441206298374314490776173/11785911707677576025107751732350000000000000000), (436398402944631816739/711098410100000000000), (-4365896738030695287981111783577811360594634903/259031026542364308244126411700000000000000000)]
    bernstein := [(6878686647132905331014379262761127049880768287711/30420736381020854050716026782770790400000000000000000), (41538191071596491612604813104374793973865219980031/141239133197596822378324410062864384000000000000000000), (827133401469933246281650904799845529066410560380139/2471684830957944391620677176100126720000000000000000000), (2148825427878568941518886313185856048270675040941249/6179212077394860979051692940250316800000000000000000000), (5150602423451781722156370073084171577462697108331587/15448030193487152447629232350625792000000000000000000000)]
    reserve := (226118347/1000000000000) }

theorem tilt_026_017_valid : tilt_026_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_026_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_026_017]
  · intro i; fin_cases i <;> norm_num [tilt_026_017]
  · norm_num [tilt_026_017]
  · norm_num [tilt_026_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_026_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_026_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_026_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_026_017]

def tilt_026_018 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/64), (3/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14570673/100000000), (14570673/100000000), (8773791/100000000), (14541661/100000000), (14541661/100000000), (16571599/100000000), (16429943/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2774467/50000000), (1/100000000), (2118977/50000000), (4291427/100000000), (1/100000000), (5573689/100000000), (15631/10000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-2259757498587903820209992225669710946107031/407800980754003958838674873300000000000000000), (278597865202776158757/430152331000000000000), (-3613276973120147047401336571994850560277107031/203900490377001979419337436650000000000000000), (278597865202776158757/430152331000000000000), (-249113592715231247964912522474621772745107139/14062102784620826166850857700000000000000000)]
    bernstein := [(1735143652762776148409425303917388365540373689321/6841765139121767282291557503126732800000000000000000), (5595328259525455968216490702666442567061054170299/17104412847804418205728893757816832000000000000000000), (15898968492891245439450132233439811023069121533233/42761032119511045514322234394542080000000000000000000), (41441103611244370700270352483773038616136993888403/106902580298777613785805585986355200000000000000000000), (100128233394930261382974122662170164956709819285689/267256450746944034464513964965888000000000000000000000)]
    reserve := (10144421/40000000000) }

theorem tilt_026_018_valid : tilt_026_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_026_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_026_018]
  · intro i; fin_cases i <;> norm_num [tilt_026_018]
  · norm_num [tilt_026_018]
  · norm_num [tilt_026_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_026_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_026_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_026_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_026_018]

def tilt_026_019 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/64), (3/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14570673/100000000), (14570673/100000000), (8773791/100000000), (14541661/100000000), (14541661/100000000), (16571599/100000000), (16429943/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2774467/50000000), (1/100000000), (2118977/50000000), (4291427/100000000), (1/100000000), (2785463/50000000), (40093/25000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-6677486716778916447322157069952795377453797/1257840185107515331630078928565625000000000000), (267098724944587/423795400000000), (-347763741695013825195739602049929545519712647629/20125442961720245306081262857050000000000000000), (267098724944587/423795400000000), (-347656901907545362532582447536810300793673386877/20125442961720245306081262857050000000000000000)]
    bernstein := [(108620827342602240874398945761791639121553205298307/337648903664460287073111460505504972800000000000000000), (331206484896161943932784247640241965784958425380233/844122259161150717682778651263762432000000000000000000), (2753445401702607493099619130763637961049191650734033/6330916943708630382620839884478218240000000000000000000), (338667750121251123119560421699977879673044824938343/753680588536741712216766652914073600000000000000000000), (5746057496588337194681638756745142971728672011221363/13189410299392979963793416425996288000000000000000000000)]
    reserve := (80424389/250000000000) }

theorem tilt_026_019_valid : tilt_026_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_026_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_026_019]
  · intro i; fin_cases i <;> norm_num [tilt_026_019]
  · norm_num [tilt_026_019]
  · norm_num [tilt_026_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_026_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_026_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_026_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_026_019]

def tilt_026_020 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/64), (3/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14570673/100000000), (14570673/100000000), (8773791/100000000), (14541661/100000000), (14541661/100000000), (16571599/100000000), (16429943/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2774467/50000000), (1/100000000), (2118977/50000000), (4291427/100000000), (1/100000000), (2785463/50000000), (40093/25000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-6882367336130559803107066104164089360797547/1257840185107515331630078928565625000000000000), (267098724944587/423795400000000), (-347757071479604645190631721830939932981253647629/20125442961720245306081262857050000000000000000), (267098724944587/423795400000000), (-347646953602226556233782008773273307551480886877/20125442961720245306081262857050000000000000000)]
    bernstein := [(53650936012002752422127329060508328303387525798307/337648903664460287073111460505504972800000000000000000), (193788591844394882530485075450660820475547338880233/844122259161150717682778651263762432000000000000000000), (1722865890986360469812563696070178193613254496234033/6330916943708630382620839884478218240000000000000000000), (215986631140241980385205311831162274894749327438343/753680588536741712216766652914073600000000000000000000), (3599266116858655256813529440168778198255683203721363/13189410299392979963793416425996288000000000000000000000)]
    reserve := (9930977/62500000000) }

theorem tilt_026_020_valid : tilt_026_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_026_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_026_020]
  · intro i; fin_cases i <;> norm_num [tilt_026_020]
  · norm_num [tilt_026_020]
  · norm_num [tilt_026_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_026_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_026_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_026_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_026_020]

def tiltBundle026_row : Alternative → Row
  | .zero => tilt_026_000
  | (.spike 0 false false) => tilt_026_001
  | (.spike 0 false true) => tilt_026_002
  | (.spike 0 true false) => tilt_026_003
  | (.spike 0 true true) => tilt_026_004
  | (.spike 1 false false) => tilt_026_005
  | (.spike 1 false true) => tilt_026_006
  | (.spike 1 true false) => tilt_026_007
  | (.spike 1 true true) => tilt_026_008
  | (.spike 2 false false) => tilt_026_009
  | (.spike 2 false true) => tilt_026_010
  | (.spike 2 true false) => tilt_026_011
  | (.spike 2 true true) => tilt_026_012
  | (.spike 3 false false) => tilt_026_013
  | (.spike 3 false true) => tilt_026_014
  | (.spike 3 true false) => tilt_026_015
  | (.spike 3 true true) => tilt_026_016
  | (.spike 4 false false) => tilt_026_017
  | (.spike 4 false true) => tilt_026_018
  | (.spike 4 true false) => tilt_026_019
  | (.spike 4 true true) => tilt_026_020

def tiltBundle026 : TiltBundle where
  interval := ⟨(1/64), (3/160)⟩
  lambda := ![(14570673/100000000), (14570673/100000000), (8773791/100000000), (14541661/100000000), (14541661/100000000), (16571599/100000000), (16429943/100000000)]
  row := tiltBundle026_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_026_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_026_001_valid | exact tilt_026_002_valid | exact tilt_026_003_valid | exact tilt_026_004_valid | exact tilt_026_005_valid | exact tilt_026_006_valid | exact tilt_026_007_valid | exact tilt_026_008_valid | exact tilt_026_009_valid | exact tilt_026_010_valid | exact tilt_026_011_valid | exact tilt_026_012_valid | exact tilt_026_013_valid | exact tilt_026_014_valid | exact tilt_026_015_valid | exact tilt_026_016_valid | exact tilt_026_017_valid | exact tilt_026_018_valid | exact tilt_026_019_valid | exact tilt_026_020_valid
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
