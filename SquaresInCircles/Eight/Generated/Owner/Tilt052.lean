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

def tilt_052_000 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11149063/50000000), (11149063/50000000), (8237941/50000000), (19463933/100000000), (19463933/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11149063/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4865983/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3984079/100000000), (1/100000000), (222833/4000000), (6443639/100000000), (1/100000000), (869421/25000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-17317820344019512170973381897386660306689/248678809916145296104066650000000000000000), (91845323199283/139270625000000), (-72768534714422084639331254638365660306689/124339404958072648052033325000000000000000), (91845323199283/139270625000000), (-128219249084824657107689127379344660306689/248678809916145296104066650000000000000000)]
    bernstein := [(129410497788030012587637664709551016013043/2988928003799823270481570312500000000000000), (137864197932307932701596629319297916013043/2974626912872551388804625000000000000000000), (52610677318318276739013925927160304904388791/1065766328212051269017428500000000000000000000), (19932366126056124958074531798493301124455791/380752244847686577766992000000000000000000000), (35208044916816744721512945856032046969510184671/636617753385331958026410624000000000000000000000)]
    reserve := (8659325191/200000000000) }

theorem tilt_052_000_valid : tilt_052_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_052_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_052_000]
  · intro i; fin_cases i <;> norm_num [tilt_052_000]
  · norm_num [tilt_052_000]
  · norm_num [tilt_052_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_052_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_052_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_052_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_052_000]

def tilt_052_001 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11149063/50000000), (11149063/50000000), (8237941/50000000), (19463933/100000000), (19463933/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11149063/100000000), 0], ![(11149/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4865983/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3984079/100000000), (1/100000000), (222833/4000000), (6443639/100000000), (1/100000000), (869421/25000000), (1/100000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-17257749086101546885242796853005315645189/248678809916145296104066650000000000000000), (91845323199283/139270625000000), (-72708463456504119353600669593984315645189/124339404958072648052033325000000000000000), (91845323199283/139270625000000), (-128159177826906691821958542334963315645189/248678809916145296104066650000000000000000)]
    bernstein := [(130191424140963561302135270286508496612543/2988928003799823270481570312500000000000000), (138645124285241481416094234896255396612543/2974626912872551388804625000000000000000000), (52891870876632272241518794519909379264870291/1065766328212051269017428500000000000000000000), (20033345910616224603387645258098341500437291/380752244847686577766992000000000000000000000), (35377791934662272225284289581628119841535086171/636617753385331958026410624000000000000000000000)]
    reserve := (43557899011/1000000000000) }

theorem tilt_052_001_valid : tilt_052_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_052_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_052_001]
  · intro i; fin_cases i <;> norm_num [tilt_052_001]
  · norm_num [tilt_052_001]
  · norm_num [tilt_052_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_052_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_052_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_052_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_052_001]

def tilt_052_002 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11149063/50000000), (11149063/50000000), (8237941/50000000), (19463933/100000000), (19463933/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11149063/100000000), 0], ![0, 0, (1321/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4865983/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3984079/100000000), (5797/100000000), (222833/4000000), (6443639/100000000), (1/100000000), (869421/25000000), (1/100000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-9152639546765050151043641663270658062553787/131053732825808571046843124550000000000000000), (91845323199283/139270625000000), (-38375166019967205841868240597766591062553787/65526866412904285523421562275000000000000000), (91845323199283/139270625000000), (-67597692493169361532692839532262524062553787/131053732825808571046843124550000000000000000)]
    bernstein := [(67859405403223842553456347058410840386800769/1575165058002506863543787554687500000000000000), (72314505379258306453512721407747456686800769/1567628383083834581900037375000000000000000000), (890433132365928851785195660856194083154378163/18118027579604871573296284500000000000000000000), (10460401781421942127608012990778169828547084053/200656433034730826483204784000000000000000000000), (18480751035419226814012619552255157181478748293093/335497556034069941879918398848000000000000000000000)]
    reserve := (10770205487/250000000000) }

theorem tilt_052_002_valid : tilt_052_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_052_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_052_002]
  · intro i; fin_cases i <;> norm_num [tilt_052_002]
  · norm_num [tilt_052_002]
  · norm_num [tilt_052_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_052_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_052_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_052_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_052_002]

def tilt_052_003 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11149063/50000000), (11149063/50000000), (8237941/50000000), (19463933/100000000), (19463933/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (2790053/25000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (9731967/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(796019/20000000), (1/100000000), (222833/4000000), (6443639/100000000), (1/100000000), (869421/25000000), (1/100000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-70297933409630380203086878086898353769/1014000555254132211056850000000000000000), (91845323199283/139270625000000), (-296401054860896400831129222717898353769/507000277627066105528425000000000000000), (91845323199283/139270625000000), (-522504176312162421459171567348898353769/1014000555254132211056850000000000000000)]
    bernstein := [(531790649871592828799067635276721401003/12187506673727550613664062500000000000000), (6228871486258442037555686465009035411033/133421125691333185665375000000000000000000), (1512025376108475184465681703622203042051177/30420016657623966331705500000000000000000000), (899877542799337480806130380891693440457421/17077904088490647765168000000000000000000000), (144456571399408275060439509836018032555356791/2595841421450578460305536000000000000000000000)]
    reserve := (43634080711/1000000000000) }

theorem tilt_052_003_valid : tilt_052_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_052_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_052_003]
  · intro i; fin_cases i <;> norm_num [tilt_052_003]
  · norm_num [tilt_052_003]
  · norm_num [tilt_052_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_052_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_052_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_052_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_052_003]

def tilt_052_004 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11149063/50000000), (11149063/50000000), (8237941/50000000), (19463933/100000000), (19463933/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (5568957/50000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4865983/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3988063/100000000), (1/100000000), (222833/4000000), (6443639/100000000), (1/100000000), (869421/25000000), (1/100000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-237771178207552350107923651264623796373/3409965531438742472591850000000000000000), (91845323199283/139270625000000), (-998129588964332759461969829995623796373/1704982765719371236295925000000000000000), (91845323199283/139270625000000), (-1758487999721113168816016008726623796373/3409965531438742472591850000000000000000)]
    bernstein := [(1770573277717632292678910087006290647151/40985162637484885487882812500000000000000), (20751425102082155451241179649644297118661/448679675189308220077875000000000000000000), (719994033884187744793749427489316209177987/14614137991880324882536500000000000000000000), (3000897972722302947646601534532362281266857/57430998424231452169968000000000000000000000), (481926555063039322270294116660232168137235147/8729511760483180729835136000000000000000000000)]
    reserve := (4320034773/100000000000) }

theorem tilt_052_004_valid : tilt_052_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_052_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_052_004]
  · intro i; fin_cases i <;> norm_num [tilt_052_004]
  · norm_num [tilt_052_004]
  · norm_num [tilt_052_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_052_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_052_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_052_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_052_004]

def tilt_052_005 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11149063/50000000), (11149063/50000000), (8237941/50000000), (19463933/100000000), (19463933/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11149063/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4865983/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3984079/100000000), (1/100000000), (222833/4000000), (3220231/50000000), (1/100000000), (869421/25000000), (1/100000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-123196017100724305870218215801634579697/1775401430188036123728255000000000000000), (91845323199283/139270625000000), (-519077265009854637664660413302934579697/887700715094018061864127500000000000000), (91845323199283/139270625000000), (-914958512918984969459102610804234579697/1775401430188036123728255000000000000000)]
    bernstein := [(929647186543952096198222382353470463939/21338959497452357256349218750000000000000), (990000987221994494659478271553900463939/21236859212775551719237500000000000000000), (377672918570484428098844373608258992438343/7608863272234440530263950000000000000000000), (143046362696946242125187645369764641529343/2718317979235270620062400000000000000000000), (252610210170887408244747103515662755120825583/4545027661281372476744332800000000000000000000)]
    reserve := (10891430609/250000000000) }

theorem tilt_052_005_valid : tilt_052_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_052_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_052_005]
  · intro i; fin_cases i <;> norm_num [tilt_052_005]
  · norm_num [tilt_052_005]
  · norm_num [tilt_052_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_052_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_052_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_052_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_052_005]

def tilt_052_006 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11149063/50000000), (11149063/50000000), (8237941/50000000), (19463933/100000000), (19463933/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11149063/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4865983/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3984079/100000000), (1/100000000), (222833/4000000), (6446817/100000000), (1/100000000), (869421/25000000), (1/100000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-6843113073780854247564691591848427951/98146531833877782132570000000000000000), (91845323199283/139270625000000), (-28727950406729032793490637230048427951/49073265916938891066285000000000000000), (91845323199283/139270625000000), (-50612787739677211339416582868248427951/98146531833877782132570000000000000000)]
    bernstein := [(662575543367629104761557195240655676281/15335395599043403458214062500000000000000), (705949233139808242314041396384915676281/15262020500483387173725000000000000000000), (269428978562327285868946747073403333897797/5468163916458905004528900000000000000000000), (102087247013115242491911482776881643986797/1953538624061873558236800000000000000000000), (180339825075731878294805386711288318761805757/3266316579431452589371929600000000000000000000)]
    reserve := (5400704689/125000000000) }

theorem tilt_052_006_valid : tilt_052_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_052_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_052_006]
  · intro i; fin_cases i <;> norm_num [tilt_052_006]
  · norm_num [tilt_052_006]
  · norm_num [tilt_052_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_052_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_052_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_052_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_052_006]

def tilt_052_007 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11149063/50000000), (11149063/50000000), (8237941/50000000), (19463933/100000000), (19463933/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11149063/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4865983/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3984079/100000000), (1/100000000), (5566939/100000000), (6443639/100000000), (1/100000000), (869421/25000000), (1/100000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-61592135214981330227820210334229806508323/887519074435484343206588850000000000000000), (91845323199283/139173475000000), (-259785108761375622245782582053549775508323/443759537217742171603294425000000000000000), (91845323199283/139173475000000), (-457978082307769914263744953772869744508323/887519074435484343206588850000000000000000)]
    bernstein := [(6049804050418319261773600505146988103093413/138674855380544428626029507812500000000000000), (495552075702340593469567898960334533891801/10616256871237850995294125000000000000000000), (1323257888756394460231155145510035601552030259/26625572233064530296197665500000000000000000000), (71595683731812567690191891488319196581509037/1358880879518444927397648000000000000000000000), (181388433786228029163229806609811126561286501/3259754419734347085522048000000000000000000000)]
    reserve := (43625818349/1000000000000) }

theorem tilt_052_007_valid : tilt_052_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_052_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_052_007]
  · intro i; fin_cases i <;> norm_num [tilt_052_007]
  · norm_num [tilt_052_007]
  · norm_num [tilt_052_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_052_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_052_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_052_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_052_007]

def tilt_052_008 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11149063/50000000), (11149063/50000000), (8237941/50000000), (19463933/100000000), (19463933/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11149063/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4865983/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3984079/100000000), (1/100000000), (696839/12500000), (6443639/100000000), (1/100000000), (869421/25000000), (1/100000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-9857359688028695396703150017872469217803/141393365698777904196384900000000000000000), (91845323199283/139367800000000), (-3758076402505986317985102935831945997073/6426971168126268372562950000000000000000), (91845323199283/139367800000000), (-72820321167103003598969114570430342717803/141393365698777904196384900000000000000000)]
    bernstein := [(73323341401706989422776920966695213418561/1699439491571849810052703125000000000000000), (859408570117171024483290490759879494479171/18604390223523408446892750000000000000000000), (2710869840451765462867913695207454739388787/55088324298225157479111000000000000000000000), (124291718721325941992458222344028856630104727/2381361948610996281202272000000000000000000000), (19961287001240946738557867898554793636998276917/361967016188871434742745344000000000000000000000)]
    reserve := (10786400717/250000000000) }

theorem tilt_052_008_valid : tilt_052_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_052_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_052_008]
  · intro i; fin_cases i <;> norm_num [tilt_052_008]
  · norm_num [tilt_052_008]
  · norm_num [tilt_052_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_052_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_052_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_052_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_052_008]

def tilt_052_009 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11149063/50000000), (11149063/50000000), (8237941/50000000), (19463933/100000000), (19463933/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11149063/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4865983/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3984079/100000000), (1/100000000), (222833/4000000), (3220231/50000000), (1/100000000), (869421/25000000), (1/100000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-492784364438119316564436842683419665413/7101605720752144494913020000000000000000), (91845323199283/139270625000000), (-2076309356074640643742205632688619665413/3550802860376072247456510000000000000000), (91845323199283/139270625000000), (-3659834347711161970919974422693819665413/7101605720752144494913020000000000000000)]
    bernstein := [(3718584897717921174706557796214424349631/85355837989809429025396875000000000000000), (3960000100430090768551581353016144349631/84947436851102206876950000000000000000000), (1510690288541063094671214506501754386201747/30435453088937762121055800000000000000000000), (572184953152576630027279531978421022440747/10873271916941082480249600000000000000000000), (1010440004158764416005083579852079309562895707/18180110645125489906977331200000000000000000000)]
    reserve := (43565677349/1000000000000) }

theorem tilt_052_009_valid : tilt_052_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_052_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_052_009]
  · intro i; fin_cases i <;> norm_num [tilt_052_009]
  · norm_num [tilt_052_009]
  · norm_num [tilt_052_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_052_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_052_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_052_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_052_009]

def tilt_052_010 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11149063/50000000), (11149063/50000000), (8237941/50000000), (19463933/100000000), (19463933/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11149063/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4865983/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3984079/100000000), (1/100000000), (222833/4000000), (3223409/50000000), (1/100000000), (869421/25000000), (1/100000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-57607542785672740346389259294308896739/826583045819916347262300000000000000000), (91845323199283/139270625000000), (-241920071837235420553534463792308896739/413291522909958173631150000000000000000), (91845323199283/139270625000000), (-426232600888798100760679668290308896739/826583045819916347262300000000000000000)]
    bernstein := [(429563994700459169001793969705184342393/9934892377643225327671875000000000000000), (457663233296870993593577138192984342393/9887357007415267311750000000000000000000), (174662493354297689098308439471531654364741/3542498767799641488267000000000000000000000), (66177727318101066494329289992066944581741/1265581696949154215904000000000000000000000), (116901161678868497123298001755898310441906621/2116052597298985848991488000000000000000000000)]
    reserve := (43237911229/1000000000000) }

theorem tilt_052_010_valid : tilt_052_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_052_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_052_010]
  · intro i; fin_cases i <;> norm_num [tilt_052_010]
  · norm_num [tilt_052_010]
  · norm_num [tilt_052_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_052_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_052_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_052_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_052_010]

def tilt_052_011 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11149063/50000000), (11149063/50000000), (8237941/50000000), (19463933/100000000), (19463933/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11149063/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(2433/12500000), 0, 0, 0, 0], ![0, 0, 0, (9731967/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3984079/100000000), (1/100000000), (222833/4000000), (6443639/100000000), (1/100000000), (869421/25000000), (1/100000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-8632691966475695859060409494547774143157/124339404958072648052033325000000000000000), (91845323199283/139270625000000), (-36358049151676982093239345865037274143157/62169702479036324026016662500000000000000), (91845323199283/139270625000000), (-64083406336878268327418282235526774143157/124339404958072648052033325000000000000000)]
    bernstein := [(65046085565957789237360491258667736138959/1494464001899911635240785156250000000000000), (69272935638096749294339973563541186138959/1487313456436275694402312500000000000000000), (26428066079264074289408386450435500135882083/532883164106025634508714250000000000000000000), (10010255866530817719659845023665330215353083/190376122423843288883496000000000000000000000), (17678108841096503920243028436163823981658532523/318308876692665979013205312000000000000000000000)]
    reserve := (43524692119/1000000000000) }

theorem tilt_052_011_valid : tilt_052_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_052_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_052_011]
  · intro i; fin_cases i <;> norm_num [tilt_052_011]
  · norm_num [tilt_052_011]
  · norm_num [tilt_052_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_052_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_052_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_052_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_052_011]

def tilt_052_012 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11149063/50000000), (11149063/50000000), (8237941/50000000), (19463933/100000000), (19463933/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11149063/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1153/20000000), 0, 0], ![0, 0, 0, (9731967/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3984079/100000000), (1/100000000), (222833/4000000), (6443639/100000000), (253/5000000), (869421/25000000), (1/100000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-1597223929674518786205918580309019044808719/22878450512285367241574131800000000000000000), (91845323199283/139270625000000), (-6698689651751555453294842872479087044808719/11439225256142683620787065900000000000000000), (91845323199283/139270625000000), (-11800155373828592120383767164649155044808719/22878450512285367241574131800000000000000000)]
    bernstein := [(11853967842177353493869888358535891617486653/274981376349583740884304468750000000000000000), (12631708255450922144354113102632606417486653/273665675984274727770025500000000000000000000), (4821531065271549977213405171745589936850386361/98050502195508716749603422000000000000000000000), (1827079809657603012796083249156564478876543361/35029206525987165154563264000000000000000000000), (3227881006254739341873264468886547204687069389841/58568833311450540138429777408000000000000000000000)]
    reserve := (43108257001/1000000000000) }

theorem tilt_052_012_valid : tilt_052_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_052_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_052_012]
  · intro i; fin_cases i <;> norm_num [tilt_052_012]
  · norm_num [tilt_052_012]
  · norm_num [tilt_052_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_052_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_052_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_052_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_052_012]

def tilt_052_013 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11149063/50000000), (11149063/50000000), (8237941/50000000), (19463933/100000000), (19463933/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11149063/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4870849/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3984079/100000000), (1/100000000), (222833/4000000), (6443639/100000000), (1/100000000), (3474207/100000000), (1/100000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-139255341453122709285284134074204594831/2007516606198213955305890000000000000000), (91845323199283/139270625000000), (-586893923774124266788975171695604594831/1003758303099106977652945000000000000000), (91845323199283/139270625000000), (-1034532506095125824292666209317004594831/2007516606198213955305890000000000000000)]
    bernstein := [(1051803307212877057910194954151500267197/24128805362959302347426562500000000000000), (1120047736358974299766364047157040267197/24013356533471458795525000000000000000000), (2990896725366432685425676795298537201172623/60225498185946418659176700000000000000000000), (161827634841596939868263844803374936089089/3073709636284346725827200000000000000000000), (285769919269004568411962210176719382945758609/5139242511867427725583078400000000000000000000)]
    reserve := (1089779717/25000000000) }

theorem tilt_052_013_valid : tilt_052_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_052_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_052_013]
  · intro i; fin_cases i <;> norm_num [tilt_052_013]
  · norm_num [tilt_052_013]
  · norm_num [tilt_052_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_052_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_052_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_052_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_052_013]

def tilt_052_014 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11149063/50000000), (11149063/50000000), (8237941/50000000), (19463933/100000000), (19463933/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11149063/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (1944447/20000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3984079/100000000), (1/100000000), (222833/4000000), (6443639/100000000), (1/100000000), (1740581/50000000), (1/100000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-13883585217601105133294886550121838723583/199142009057823123958640260000000000000000), (91845323199283/139270625000000), (-58288521316245918170728679611649438723583/99571004528911561979320130000000000000000), (91845323199283/139270625000000), (-102693457414890731208162472673177038723583/199142009057823123958640260000000000000000)]
    bernstein := [(103430781481619502254756245304925536593421/2393533762714220239887503125000000000000000), (2093809598261807990947843112415324035274999/45259547513141619081509150000000000000000000), (98135807251921378652301528322370747328118613/1991420090578231239586402600000000000000000000), (302780758818045697590699276037516940567482563/5793222081682127242433171200000000000000000000), (28150880721494352867160766572569961849969378337/509803543188027197334119065600000000000000000000)]
    reserve := (43212585129/1000000000000) }

theorem tilt_052_014_valid : tilt_052_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_052_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_052_014]
  · intro i; fin_cases i <;> norm_num [tilt_052_014]
  · norm_num [tilt_052_014]
  · norm_num [tilt_052_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_052_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_052_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_052_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_052_014]

def tilt_052_015 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11149063/50000000), (11149063/50000000), (8237941/50000000), (19463933/100000000), (19463933/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11149063/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(2433/12500000), 0, 0, 0, 0], ![0, 0, 0, (9731967/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3984079/100000000), (1/100000000), (222833/4000000), (6443639/100000000), (1/100000000), (869421/25000000), (1/100000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-8632691966475695859060409494547774143157/124339404958072648052033325000000000000000), (91845323199283/139270625000000), (-36358049151676982093239345865037274143157/62169702479036324026016662500000000000000), (91845323199283/139270625000000), (-64083406336878268327418282235526774143157/124339404958072648052033325000000000000000)]
    bernstein := [(65046085565957789237360491258667736138959/1494464001899911635240785156250000000000000), (69272935638096749294339973563541186138959/1487313456436275694402312500000000000000000), (26428066079264074289408386450435500135882083/532883164106025634508714250000000000000000000), (10010255866530817719659845023665330215353083/190376122423843288883496000000000000000000000), (17678108841096503920243028436163823981658532523/318308876692665979013205312000000000000000000000)]
    reserve := (43524692119/1000000000000) }

theorem tilt_052_015_valid : tilt_052_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_052_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_052_015]
  · intro i; fin_cases i <;> norm_num [tilt_052_015]
  · norm_num [tilt_052_015]
  · norm_num [tilt_052_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_052_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_052_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_052_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_052_015]

def tilt_052_016 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11149063/50000000), (11149063/50000000), (8237941/50000000), (19463933/100000000), (19463933/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11149063/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1153/20000000), 0, 0], ![0, 0, 0, (9731967/100000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3984079/100000000), (1/100000000), (222833/4000000), (6443639/100000000), (253/5000000), (869421/25000000), (1/100000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-1597223929674518786205918580309019044808719/22878450512285367241574131800000000000000000), (91845323199283/139270625000000), (-6698689651751555453294842872479087044808719/11439225256142683620787065900000000000000000), (91845323199283/139270625000000), (-11800155373828592120383767164649155044808719/22878450512285367241574131800000000000000000)]
    bernstein := [(11853967842177353493869888358535891617486653/274981376349583740884304468750000000000000000), (12631708255450922144354113102632606417486653/273665675984274727770025500000000000000000000), (4821531065271549977213405171745589936850386361/98050502195508716749603422000000000000000000000), (1827079809657603012796083249156564478876543361/35029206525987165154563264000000000000000000000), (3227881006254739341873264468886547204687069389841/58568833311450540138429777408000000000000000000000)]
    reserve := (43108257001/1000000000000) }

theorem tilt_052_016_valid : tilt_052_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_052_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_052_016]
  · intro i; fin_cases i <;> norm_num [tilt_052_016]
  · norm_num [tilt_052_016]
  · norm_num [tilt_052_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_052_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_052_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_052_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_052_016]

def tilt_052_017 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11149063/50000000), (11149063/50000000), (8237941/50000000), (19463933/100000000), (19463933/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11149063/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4865983/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3984079/100000000), (1/100000000), (222833/4000000), (6443639/100000000), (1/100000000), (869421/25000000), (1/100000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-17317820344019512170973381897386660306689/248678809916145296104066650000000000000000), (91845323199283/139270625000000), (-72768534714422084639331254638365660306689/124339404958072648052033325000000000000000), (91845323199283/139270625000000), (-128219249084824657107689127379344660306689/248678809916145296104066650000000000000000)]
    bernstein := [(129410497788030012587637664709551016013043/2988928003799823270481570312500000000000000), (137864197932307932701596629319297916013043/2974626912872551388804625000000000000000000), (52610677318318276739013925927160304904388791/1065766328212051269017428500000000000000000000), (19932366126056124958074531798493301124455791/380752244847686577766992000000000000000000000), (35208044916816744721512945856032046969510184671/636617753385331958026410624000000000000000000000)]
    reserve := (8659325191/200000000000) }

theorem tilt_052_017_valid : tilt_052_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_052_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_052_017]
  · intro i; fin_cases i <;> norm_num [tilt_052_017]
  · norm_num [tilt_052_017]
  · norm_num [tilt_052_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_052_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_052_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_052_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_052_017]

def tilt_052_018 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11149063/50000000), (11149063/50000000), (8237941/50000000), (19463933/100000000), (19463933/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11149063/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4865983/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3984079/100000000), (1/100000000), (222833/4000000), (6443639/100000000), (1/100000000), (869421/25000000), (1/100000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-17317820344019512170973381897386660306689/248678809916145296104066650000000000000000), (91845323199283/139270625000000), (-72768534714422084639331254638365660306689/124339404958072648052033325000000000000000), (91845323199283/139270625000000), (-128219249084824657107689127379344660306689/248678809916145296104066650000000000000000)]
    bernstein := [(129410497788030012587637664709551016013043/2988928003799823270481570312500000000000000), (137864197932307932701596629319297916013043/2974626912872551388804625000000000000000000), (52610677318318276739013925927160304904388791/1065766328212051269017428500000000000000000000), (19932366126056124958074531798493301124455791/380752244847686577766992000000000000000000000), (35208044916816744721512945856032046969510184671/636617753385331958026410624000000000000000000000)]
    reserve := (8659325191/200000000000) }

theorem tilt_052_018_valid : tilt_052_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_052_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_052_018]
  · intro i; fin_cases i <;> norm_num [tilt_052_018]
  · norm_num [tilt_052_018]
  · norm_num [tilt_052_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_052_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_052_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_052_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_052_018]

def tilt_052_019 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11149063/50000000), (11149063/50000000), (8237941/50000000), (19463933/100000000), (19463933/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11149063/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4865983/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3984079/100000000), (1/100000000), (222833/4000000), (6443639/100000000), (1/100000000), (869421/25000000), (1/100000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-17317820344019512170973381897386660306689/248678809916145296104066650000000000000000), (91845323199283/139270625000000), (-72768534714422084639331254638365660306689/124339404958072648052033325000000000000000), (91845323199283/139270625000000), (-128219249084824657107689127379344660306689/248678809916145296104066650000000000000000)]
    bernstein := [(129410497788030012587637664709551016013043/2988928003799823270481570312500000000000000), (137864197932307932701596629319297916013043/2974626912872551388804625000000000000000000), (52610677318318276739013925927160304904388791/1065766328212051269017428500000000000000000000), (19932366126056124958074531798493301124455791/380752244847686577766992000000000000000000000), (35208044916816744721512945856032046969510184671/636617753385331958026410624000000000000000000000)]
    reserve := (8659325191/200000000000) }

theorem tilt_052_019_valid : tilt_052_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_052_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_052_019]
  · intro i; fin_cases i <;> norm_num [tilt_052_019]
  · norm_num [tilt_052_019]
  · norm_num [tilt_052_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_052_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_052_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_052_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_052_019]

def tilt_052_020 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(11149063/50000000), (11149063/50000000), (8237941/50000000), (19463933/100000000), (19463933/100000000), 0, 0]
    cone := fun i => (![![0, 0, 0, (11149063/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, (4865983/50000000), 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(3984079/100000000), (1/100000000), (222833/4000000), (6443639/100000000), (1/100000000), (869421/25000000), (1/100000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-17317820344019512170973381897386660306689/248678809916145296104066650000000000000000), (91845323199283/139270625000000), (-72768534714422084639331254638365660306689/124339404958072648052033325000000000000000), (91845323199283/139270625000000), (-128219249084824657107689127379344660306689/248678809916145296104066650000000000000000)]
    bernstein := [(129410497788030012587637664709551016013043/2988928003799823270481570312500000000000000), (137864197932307932701596629319297916013043/2974626912872551388804625000000000000000000), (52610677318318276739013925927160304904388791/1065766328212051269017428500000000000000000000), (19932366126056124958074531798493301124455791/380752244847686577766992000000000000000000000), (35208044916816744721512945856032046969510184671/636617753385331958026410624000000000000000000000)]
    reserve := (8659325191/200000000000) }

theorem tilt_052_020_valid : tilt_052_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_052_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_052_020]
  · intro i; fin_cases i <;> norm_num [tilt_052_020]
  · norm_num [tilt_052_020]
  · norm_num [tilt_052_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_052_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_052_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_052_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_052_020]

def tiltBundle052_row : Alternative → Row
  | .zero => tilt_052_000
  | (.spike 0 false false) => tilt_052_001
  | (.spike 0 false true) => tilt_052_002
  | (.spike 0 true false) => tilt_052_003
  | (.spike 0 true true) => tilt_052_004
  | (.spike 1 false false) => tilt_052_005
  | (.spike 1 false true) => tilt_052_006
  | (.spike 1 true false) => tilt_052_007
  | (.spike 1 true true) => tilt_052_008
  | (.spike 2 false false) => tilt_052_009
  | (.spike 2 false true) => tilt_052_010
  | (.spike 2 true false) => tilt_052_011
  | (.spike 2 true true) => tilt_052_012
  | (.spike 3 false false) => tilt_052_013
  | (.spike 3 false true) => tilt_052_014
  | (.spike 3 true false) => tilt_052_015
  | (.spike 3 true true) => tilt_052_016
  | (.spike 4 false false) => tilt_052_017
  | (.spike 4 false true) => tilt_052_018
  | (.spike 4 true false) => tilt_052_019
  | (.spike 4 true true) => tilt_052_020

def tiltBundle052 : TiltBundle where
  interval := ⟨(1/5), (9/40)⟩
  lambda := ![(11149063/50000000), (11149063/50000000), (8237941/50000000), (19463933/100000000), (19463933/100000000), 0, 0]
  row := tiltBundle052_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_052_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_052_001_valid | exact tilt_052_002_valid | exact tilt_052_003_valid | exact tilt_052_004_valid | exact tilt_052_005_valid | exact tilt_052_006_valid | exact tilt_052_007_valid | exact tilt_052_008_valid | exact tilt_052_009_valid | exact tilt_052_010_valid | exact tilt_052_011_valid | exact tilt_052_012_valid | exact tilt_052_013_valid | exact tilt_052_014_valid | exact tilt_052_015_valid | exact tilt_052_016_valid | exact tilt_052_017_valid | exact tilt_052_018_valid | exact tilt_052_019_valid | exact tilt_052_020_valid
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
