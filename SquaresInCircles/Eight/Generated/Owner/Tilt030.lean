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

def tilt_030_000 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/320), (1/32)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(732003/5000000), (732003/5000000), (4496179/50000000), (3646527/25000000), (3646527/25000000), (8197191/50000000), (4040231/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5510017/100000000), (1/100000000), (4231163/100000000), (2164887/50000000), (1/100000000), (2772403/50000000), (13181/5000000)]
    alternative := .zero
    polynomial := [(-883239850529668749974614277460365666381454289/92219476401914495396890715900550000000000000000), (16775479250669/26444768750000), (-477805043873381268295851428939892965011481454289/46109738200957247698445357950275000000000000000), (16775479250669/26444768750000), (-19484221385637405466157719257190317639930233761/1882030130651316232589606446950000000000000000)]
    bernstein := [(72158977643265230283342323938006962192059114744406671/966991296876138939252900793161351168000000000000000000000), (11148924861099632053670604390948989730842121859148759/96699129687613893925290079316135116800000000000000000000), (4035520447533884963000867978602549055463936971031197/29009738906284168177587023794840535040000000000000000000), (5649574561721258540574281938034343390140218673599/38679651875045557570116031726454046720000000000000000), (21064068598275362734058977288741368421967340191/154718607500182230280464126905816186880000000000000)]
    reserve := (37311079/500000000000) }

theorem tilt_030_000_valid : tilt_030_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_030_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_030_000]
  · intro i; fin_cases i <;> norm_num [tilt_030_000]
  · norm_num [tilt_030_000]
  · norm_num [tilt_030_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_030_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_030_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_030_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_030_000]

def tilt_030_001 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/320), (1/32)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(732003/5000000), (732003/5000000), (4496179/50000000), (3646527/25000000), (3646527/25000000), (8197191/50000000), (4040231/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(183/1250000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5510017/100000000), (1/100000000), (4231163/100000000), (2164887/50000000), (1/100000000), (2772403/50000000), (66907/25000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-4404430325106531878795551920304934496728297867/468107769336385186519973228795850000000000000000), (8839045958769587160277/14154721142050000000000), (-2390115425891082854886146174319093390515882297867/234053884668192593259986614397925000000000000000), (8839045958769587160277/14154721142050000000000), (-4775826421457059177893496796717881846535036297867/468107769336385186519973228795850000000000000000)]
    bernstein := [(410878191316144936122717834398734775090223624839685013/4908465723396694333403674483578372096000000000000000000000), (60498680979049225123624873830039961590859485022431277/490846572339669433340367448357837209600000000000000000000), (21526407367373653905648706197102315399527401733848591/147253971701900830002110234507351162880000000000000000000), (29941556055232216630617130265816410461333066405797/196338628935867773336146979343134883840000000000000000), (111670144650862958991211361994759189902421685573/785354515743471093344587917372539535360000000000000)]
    reserve := (83708069/1000000000000) }

theorem tilt_030_001_valid : tilt_030_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_030_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_030_001]
  · intro i; fin_cases i <;> norm_num [tilt_030_001]
  · norm_num [tilt_030_001]
  · norm_num [tilt_030_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_030_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_030_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_030_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_030_001]

def tilt_030_002 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/320), (1/32)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(732003/5000000), (732003/5000000), (4496179/50000000), (3646527/25000000), (3646527/25000000), (8197191/50000000), (4040231/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (4337/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5510017/100000000), (1903/50000000), (4231163/100000000), (2164887/50000000), (1/100000000), (2772403/50000000), (51923/20000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-6722195564022577642803839564389514600267069910811/691310029188316658339254676364706950000000000000000), (8850462054351363973723/13730917278062500000000), (-3635377938171972873117053373908451931634366051910811/345655014594158329169627338182353475000000000000000), (8850462054351363973723/13730917278062500000000), (-7264033680779923168591302908252514348668465033910811/691310029188316658339254676364706950000000000000000)]
    bernstein := [(673394470856473813568752754527992851961109466063970292229/7248911051661683283347423115237989548032000000000000000000000), (97670237667248716262860457119097154493713863162790189341/724891105166168328334742311523798954803200000000000000000000), (34679279521233790085103511514565671446173115973885611103/217467331549850498500422693457139686440960000000000000000000), (48447422566897325941303608116300063765265718485364501/289956442066467331333896924609519581921280000000000000000), (182767059878842981461144871623977146010407207318709/1159825768265869325335587698438078327685120000000000000)]
    reserve := (23223987/250000000000) }

theorem tilt_030_002_valid : tilt_030_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_030_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_030_002]
  · intro i; fin_cases i <;> norm_num [tilt_030_002]
  · norm_num [tilt_030_002]
  · norm_num [tilt_030_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_030_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_030_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_030_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_030_002]

def tilt_030_003 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/320), (1/32)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(732003/5000000), (732003/5000000), (4496179/50000000), (3646527/25000000), (3646527/25000000), (8197191/50000000), (4040231/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1376819/25000000), (1/100000000), (4231163/100000000), (2164887/50000000), (1/100000000), (2772403/50000000), (66907/25000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-547001674642889755371546188193905535580863959/58484363194337922743182373202975000000000000000), (8839045958769587160277/14154721142050000000000), (-298612527353071101053690360502240261765319863959/29242181597168961371591186601487500000000000000), (8839045958769587160277/14154721142050000000000), (-596678053031499312352009174816286617995058863959/58484363194337922743182373202975000000000000000)]
    bernstein := [(85763453558178557363290624485436822987072888346665801/613252996208660816783552001636827136000000000000000000000), (11001798438052455234104558231820369399396490577022529/61325299620866081678355200163682713600000000000000000000), (3722524011890602704188950314197196738863252770880107/18397589886259824503506560049104814080000000000000000000), (5118378127644767167308245073320155131986323452569/24530119848346432671342080065473085440000000000000000), (19462543627555647423138207563324688340504084921/98120479393385730685368320261892341760000000000000)]
    reserve := (27970007/200000000000) }

theorem tilt_030_003_valid : tilt_030_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_030_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_030_003]
  · intro i; fin_cases i <;> norm_num [tilt_030_003]
  · norm_num [tilt_030_003]
  · norm_num [tilt_030_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_030_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_030_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_030_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_030_003]

def tilt_030_004 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/320), (1/32)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(732003/5000000), (732003/5000000), (4496179/50000000), (3646527/25000000), (3646527/25000000), (8197191/50000000), (4040231/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5512759/100000000), (1/100000000), (4231163/100000000), (2164887/50000000), (1/100000000), (2772403/50000000), (51923/20000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-219463087713543206027186889814413365758238797/22715910802072413290001636498909375000000000000), (8850462054351363973723/13730917278062500000000), (-119454273375784934164371841941669623980885613797/11357955401036206645000818249454687500000000000), (8850462054351363973723/13730917278062500000000), (-238689083663856325122716496993524834596012988797/22715910802072413290001636498909375000000000000)]
    bernstein := [(37072482571146767453855953550499518563173207522109283/238193588851938828379767559934803968000000000000000000000), (4704025736779439968496571824218360898894742122196107/23819358885193882837976755993480396800000000000000000000), (1587972303309726420023064559115440841604288777883481/7145807665558164851393026798044119040000000000000000000), (2189918557863519976365800458764895125734911257427/9527743554077553135190702397392158720000000000000000), (8397712533656620969863828920822282899266440243/38110974216310212540762809589568634880000000000000)]
    reserve := (19455017/125000000000) }

theorem tilt_030_004_valid : tilt_030_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_030_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_030_004]
  · intro i; fin_cases i <;> norm_num [tilt_030_004]
  · norm_num [tilt_030_004]
  · norm_num [tilt_030_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_030_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_030_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_030_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_030_004]

def tilt_030_005 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/320), (1/32)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(732003/5000000), (732003/5000000), (4496179/50000000), (3646527/25000000), (3646527/25000000), (8197191/50000000), (4040231/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5510017/100000000), (1/100000000), (4231163/100000000), (27049/625000), (1/100000000), (2772403/50000000), (66907/25000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-88116130733542611073871946420319428418704887/9357973549865564649002931508720000000000000000), (8839045958769587160277/14154721142050000000000), (-47781023312726205367901975758038998054591504887/4678986774932782324501465754360000000000000000), (8839045958769587160277/14154721142050000000000), (-95473930494718868124730079569657676680764304887/9357973549865564649002931508720000000000000000)]
    bernstein := [(7511588426420356890840039741665195435068960321050793/98125464730238343173928979096875827200000000000000000000), (1139196505095719556264326477405055964628481163092897/9812546473023834317392897909687582720000000000000000000), (409262927404490382636051821195621714434181871719051/2943763941907150295217869372906274816000000000000000000), (570463769697749288516161224236021714960325498617/3925018589209533726957159163875033088000000000000000), (2119994846776765274443304449429648336254364953/15700074356838134907828636655500132352000000000000)]
    reserve := (76550857/1000000000000) }

theorem tilt_030_005_valid : tilt_030_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_030_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_030_005]
  · intro i; fin_cases i <;> norm_num [tilt_030_005]
  · norm_num [tilt_030_005]
  · norm_num [tilt_030_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_030_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_030_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_030_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_030_005]

def tilt_030_006 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/320), (1/32)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(732003/5000000), (732003/5000000), (4496179/50000000), (3646527/25000000), (3646527/25000000), (8197191/50000000), (4040231/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5510017/100000000), (1/100000000), (4231163/100000000), (1082927/25000000), (1/100000000), (2772403/50000000), (51923/20000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-70175299075380609121670665245099401033438319/7268721175070701246758688711546000000000000000), (8850462054351363973723/13730917278062500000000), (-38223370999569733196968947933737182161484398319/3634360587535350623379344355773000000000000000), (8850462054351363973723/13730917278062500000000), (-76376566700064085784816225202229264921935358319/7268721175070701246758688711546000000000000000)]
    bernstein := [(12380478344235817592354995933160724191129385518561841/76218065748709356305212387743980584960000000000000000000), (1557004928060311909656581351868180070872271354323689/7621806574870935630521238774398058496000000000000000000), (523664678449615001067253595865529449320484538388387/2286541972461280689156371632319417548800000000000000000), (721459430842702167050071692027941686543395579649/3048722629948374252208495509759223398400000000000000), (2770023967353148035420627736804728832758271521/12194890519793497008833982039036893593600000000000)]
    reserve := (81217479/500000000000) }

theorem tilt_030_006_valid : tilt_030_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_030_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_030_006]
  · intro i; fin_cases i <;> norm_num [tilt_030_006]
  · norm_num [tilt_030_006]
  · norm_num [tilt_030_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_030_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_030_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_030_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_030_006]

def tilt_030_007 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/320), (1/32)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(732003/5000000), (732003/5000000), (4496179/50000000), (3646527/25000000), (3646527/25000000), (8197191/50000000), (4040231/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5510017/100000000), (1/100000000), (211459/5000000), (2164887/50000000), (1/100000000), (2772403/50000000), (66907/25000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-220285361447436881922689230663699309342683019/23394419169411028399597703749050000000000000000), (441848372835129015461/707404365650000000000), (-119453571304722460632694950761316602036256183019/11697209584705514199798851874525000000000000000), (441848372835129015461/707404365650000000000), (-238686857247997484383467212291969504763169683019/23394419169411028399597703749050000000000000000)]
    bernstein := [(19726684406700816767444608641619128778724126494685141/245308264749843385151365618063638528000000000000000000000), (2945207722048068546702186817571645885006280160545389/24530826474984338515136561806363852800000000000000000000), (1053054885162491430946787625610304570841606090145487/7359247942495301554540968541909155840000000000000000000), (1466998482466804877090432266914053529381046829029/9812330589993735406054624722545541120000000000000000), (5467241120407500579655069146140616547488925061/39249322359974941624218498890182164480000000000000)]
    reserve := (40207949/500000000000) }

theorem tilt_030_007_valid : tilt_030_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_030_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_030_007]
  · intro i; fin_cases i <;> norm_num [tilt_030_007]
  · norm_num [tilt_030_007]
  · norm_num [tilt_030_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_030_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_030_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_030_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_030_007]

def tilt_030_008 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/320), (1/32)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(732003/5000000), (732003/5000000), (4496179/50000000), (3646527/25000000), (3646527/25000000), (8197191/50000000), (4040231/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5510017/100000000), (1/100000000), (4233147/100000000), (2164887/50000000), (1/100000000), (2772403/50000000), (51923/20000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-23392294913152964488755110002540695846519857/2422960888821349768051581504999000000000000000), (2950869596071338705929/4579118576687500000000), (-12741029984712583824458876849234878271713959857/1211480444410674884025790752499500000000000000), (2950869596071338705929/4579118576687500000000), (-25458667674512014684428998588467215847581399857/2422960888821349768051581504999000000000000000)]
    bernstein := [(4028795938432698342682195585073958055011556070456623/25406586369567356543844551281858314240000000000000000000), (508945628463259575366400052806861497112473686766967/2540658636956735654384455128185831424000000000000000000), (171462272193592851395155392545628046759133125108861/762197591087020696315336538455749427200000000000000000), (236262003519509676855365919538775707528524175967/1016263454782694261753782051274332569600000000000000), (906039944745985210634341686872619962127573823/4065053819130777047015128205097330278400000000000)]
    reserve := (79286447/500000000000) }

theorem tilt_030_008_valid : tilt_030_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_030_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_030_008]
  · intro i; fin_cases i <;> norm_num [tilt_030_008]
  · norm_num [tilt_030_008]
  · norm_num [tilt_030_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_030_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_030_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_030_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_030_008]

def tilt_030_009 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/320), (1/32)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(732003/5000000), (732003/5000000), (4496179/50000000), (3646527/25000000), (3646527/25000000), (8197191/50000000), (4040231/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5510017/100000000), (1/100000000), (4231163/100000000), (27049/625000), (1/100000000), (2772403/50000000), (66907/25000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-22029210925051955174126376664059966861258253/2339493387466391162250732877180000000000000000), (8839045958769587160277/14154721142050000000000), (-11945256006423217644381152329568729623404458253/1169746693733195581125366438590000000000000000), (8839045958769587160277/14154721142050000000000), (-23868482801921383333588178282473399279947658253/2339493387466391162250732877180000000000000000)]
    bernstein := [(1876025149285444579596420364857436964359539145555667/24531366182559585793482244774218956800000000000000000000), (284611914102219640851571812570906895151182342472443/2453136618255958579348224477421895680000000000000000000), (34086521028244397493645506135382929627718759498723/245313661825595857934822447742189568000000000000000000), (142541043672082054549733877765032488036502605123/981254647302383431739289790968758272000000000000000), (529699087453136974699072423211847583249196707/3925018589209533726957159163875033088000000000000)]
    reserve := (19118637/250000000000) }

theorem tilt_030_009_valid : tilt_030_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_030_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_030_009]
  · intro i; fin_cases i <;> norm_num [tilt_030_009]
  · norm_num [tilt_030_009]
  · norm_num [tilt_030_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_030_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_030_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_030_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_030_009]

def tilt_030_010 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/320), (1/32)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(732003/5000000), (732003/5000000), (4496179/50000000), (3646527/25000000), (3646527/25000000), (8197191/50000000), (4040231/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5510017/100000000), (1/100000000), (4231163/100000000), (4331709/100000000), (1/100000000), (2772403/50000000), (51923/20000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-6976927438719926803247326234709688597592021379/726872285309728454154708321059550000000000000000), (8850462054351363973723/13730917278062500000000), (-3822297378276881029858932094677609609880150021379/363436142654864227077354160529775000000000000000), (8850462054351363973723/13730917278062500000000), (-7637617829115042132914616863120509531162708021379/726872285309728454154708321059550000000000000000)]
    bernstein := [(1664486690506851188710288412773682442053079471724737181/7621808334409338235437274324633387008000000000000000000000), (198348130810535279953467466797932757981606735153826549/762180833440933823543727432463338700800000000000000000000), (65161925739222147558533200968257556957379739268089767/228654250032280147063118229739001610240000000000000000000), (89208163313567508643565153353767909625000322687789/304872333376373529417490972985335480320000000000000000), (345257934049448359525784397800327092436118909901/1219489333505494117669963891941341921280000000000000)]
    reserve := (218384747/1000000000000) }

theorem tilt_030_010_valid : tilt_030_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_030_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_030_010]
  · intro i; fin_cases i <;> norm_num [tilt_030_010]
  · norm_num [tilt_030_010]
  · norm_num [tilt_030_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_030_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_030_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_030_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_030_010]

def tilt_030_011 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/320), (1/32)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(732003/5000000), (732003/5000000), (4496179/50000000), (3646527/25000000), (3646527/25000000), (8197191/50000000), (4040231/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7293/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5510017/100000000), (1/100000000), (4231163/100000000), (2164887/50000000), (1/100000000), (2772403/50000000), (66907/25000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-4404704177588646293951191464886440361502633867/468107769336385186519973228795850000000000000000), (8839045958769587160277/14154721142050000000000), (-2390115699743564969301301813863674896380656633867/234053884668192593259986614397925000000000000000), (8839045958769587160277/14154721142050000000000), (-4775826695309541292308652436262463352399810633867/468107769336385186519973228795850000000000000000)]
    bernstein := [(408002095232487451497507213979558154724534880024389013/4908465723396694333403674483578372096000000000000000000000), (60211046112474879050462203201570867982015465686047277/490846572339669433340367448357837209600000000000000000000), (21440109048848367583808274229498413050126872154776591/147253971701900830002110234507351162880000000000000000000), (29826480777575400352480992876766412530374110181797/196338628935867773336146979343134883840000000000000000), (111209798628428627114581287553247831216762869573/785354515743471093344587917372539535360000000000000)]
    reserve := (83122123/1000000000000) }

theorem tilt_030_011_valid : tilt_030_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_030_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_030_011]
  · intro i; fin_cases i <;> norm_num [tilt_030_011]
  · norm_num [tilt_030_011]
  · norm_num [tilt_030_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_030_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_030_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_030_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_030_011]

def tilt_030_012 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/320), (1/32)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(732003/5000000), (732003/5000000), (4496179/50000000), (3646527/25000000), (3646527/25000000), (8197191/50000000), (4040231/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4321/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5510017/100000000), (1/100000000), (4231163/100000000), (2164887/50000000), (237/6250000), (2772403/50000000), (51923/20000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-1116189341333501668065868289809513078003959278239/114794518772206024190858895287045400000000000000000), (8850462054351363973723/13730917278062500000000), (-603667537036610586991167735264441002191390863278239/57397259386103012095429447643522700000000000000000), (8850462054351363973723/13730917278062500000000), (-1206218884731887672314269602239072491304777767278239/114794518772206024190858895287045400000000000000000)]
    bernstein := [(112401712459072356808452552888956197770406119395843710721/1203707773160847040219540569845089173504000000000000000000000), (16276713312468803638373941687822780730162134102310481209/120370777316084704021954056984508917350400000000000000000000), (5776086418747706816157068301786999570137375591404534547/36111233194825411206586217095352675205120000000000000000000), (8068160735507763548059979516692195515559511577636049/48148310926433881608781622793803566940160000000000000000), (30442304579524807746146734666587588782730236704241/192593243705735526435126491175214267760640000000000000)]
    reserve := (5836223/62500000000) }

theorem tilt_030_012_valid : tilt_030_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_030_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_030_012]
  · intro i; fin_cases i <;> norm_num [tilt_030_012]
  · norm_num [tilt_030_012]
  · norm_num [tilt_030_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_030_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_030_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_030_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_030_012]

def tilt_030_013 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/320), (1/32)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(732003/5000000), (732003/5000000), (4496179/50000000), (3646527/25000000), (3646527/25000000), (8197191/50000000), (4040231/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5510017/100000000), (1/100000000), (4231163/100000000), (2164887/50000000), (1/100000000), (5542053/100000000), (66907/25000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-1458526112970543385952626265254009223834526533/155958451168776781496567970852225000000000000000), (8839045958769587160277/14154721142050000000000), (-796300688917188026609703318289289521560143526533/77979225584388390748283985426112500000000000000), (8839045958769587160277/14154721142050000000000), (-1591142851721405509833454010313325033896452526533/155958451168776781496567970852225000000000000000)]
    bernstein := [(230240474309769422720954401391099596531195656472706587/1635342888927512824345452566043426816000000000000000000000), (29491942013761855692862745620671595600110174528805123/163534288892751282434545256604342681600000000000000000000), (524888412159593884466964078621382404536785632899611/2582120350938178143703346156910673920000000000000000000), (13710546715590112748347169291086796131267910894603/65413715557100512973818102641737072640000000000000000), (52146291272065215591727843252668862405629298027/261654862228402051895272410566948290560000000000000)]
    reserve := (28158067/200000000000) }

theorem tilt_030_013_valid : tilt_030_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_030_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_030_013]
  · intro i; fin_cases i <;> norm_num [tilt_030_013]
  · norm_num [tilt_030_013]
  · norm_num [tilt_030_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_030_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_030_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_030_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_030_013]

def tilt_030_014 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/320), (1/32)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(732003/5000000), (732003/5000000), (4496179/50000000), (3646527/25000000), (3646527/25000000), (8197191/50000000), (4040231/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5510017/100000000), (1/100000000), (4231163/100000000), (2164887/50000000), (1/100000000), (138689/2500000), (51923/20000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-17559711466270476842388175932540126128051477/1817271123939161877036511232595000000000000000), (8850462054351363973723/13730917278062500000000), (-9556335400139425192775227952089969486470251477/908635561969580938518255616297500000000000000), (8850462054351363973723/13730917278062500000000), (-19095111088812579908708067728247398846812451477/1817271123939161877036511232595000000000000000)]
    bernstein := [(2937636200610771715270621732961951549815388067881803/19055468860556306043754368022295347200000000000000000000), (373505494772301451119089356877048216131432064715187/1905546886055630604375436802229534720000000000000000000), (126192724529837989573724572465265277777381031551121/571664065816689181312631040668860416000000000000000000), (174066626492174954243453951900878008719823483707/762218754422252241750174720891813888000000000000000), (667309158147215204242163924973919066327870363/3048875017689008967000698883567255552000000000000)]
    reserve := (154162367/1000000000000) }

theorem tilt_030_014_valid : tilt_030_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_030_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_030_014]
  · intro i; fin_cases i <;> norm_num [tilt_030_014]
  · norm_num [tilt_030_014]
  · norm_num [tilt_030_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_030_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_030_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_030_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_030_014]

def tilt_030_015 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/320), (1/32)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(732003/5000000), (732003/5000000), (4496179/50000000), (3646527/25000000), (3646527/25000000), (8197191/50000000), (4040231/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7293/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5510017/100000000), (1/100000000), (4231163/100000000), (2164887/50000000), (1/100000000), (2772403/50000000), (66907/25000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-4404704177588646293951191464886440361502633867/468107769336385186519973228795850000000000000000), (8839045958769587160277/14154721142050000000000), (-2390115699743564969301301813863674896380656633867/234053884668192593259986614397925000000000000000), (8839045958769587160277/14154721142050000000000), (-4775826695309541292308652436262463352399810633867/468107769336385186519973228795850000000000000000)]
    bernstein := [(408002095232487451497507213979558154724534880024389013/4908465723396694333403674483578372096000000000000000000000), (60211046112474879050462203201570867982015465686047277/490846572339669433340367448357837209600000000000000000000), (21440109048848367583808274229498413050126872154776591/147253971701900830002110234507351162880000000000000000000), (29826480777575400352480992876766412530374110181797/196338628935867773336146979343134883840000000000000000), (111209798628428627114581287553247831216762869573/785354515743471093344587917372539535360000000000000)]
    reserve := (83122123/1000000000000) }

theorem tilt_030_015_valid : tilt_030_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_030_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_030_015]
  · intro i; fin_cases i <;> norm_num [tilt_030_015]
  · norm_num [tilt_030_015]
  · norm_num [tilt_030_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_030_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_030_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_030_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_030_015]

def tilt_030_016 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/320), (1/32)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(732003/5000000), (732003/5000000), (4496179/50000000), (3646527/25000000), (3646527/25000000), (8197191/50000000), (4040231/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4321/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5510017/100000000), (1/100000000), (4231163/100000000), (2164887/50000000), (237/6250000), (2772403/50000000), (51923/20000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-1116189341333501668065868289809513078003959278239/114794518772206024190858895287045400000000000000000), (8850462054351363973723/13730917278062500000000), (-603667537036610586991167735264441002191390863278239/57397259386103012095429447643522700000000000000000), (8850462054351363973723/13730917278062500000000), (-1206218884731887672314269602239072491304777767278239/114794518772206024190858895287045400000000000000000)]
    bernstein := [(112401712459072356808452552888956197770406119395843710721/1203707773160847040219540569845089173504000000000000000000000), (16276713312468803638373941687822780730162134102310481209/120370777316084704021954056984508917350400000000000000000000), (5776086418747706816157068301786999570137375591404534547/36111233194825411206586217095352675205120000000000000000000), (8068160735507763548059979516692195515559511577636049/48148310926433881608781622793803566940160000000000000000), (30442304579524807746146734666587588782730236704241/192593243705735526435126491175214267760640000000000000)]
    reserve := (5836223/62500000000) }

theorem tilt_030_016_valid : tilt_030_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_030_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_030_016]
  · intro i; fin_cases i <;> norm_num [tilt_030_016]
  · norm_num [tilt_030_016]
  · norm_num [tilt_030_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_030_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_030_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_030_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_030_016]

def tilt_030_017 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/320), (1/32)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(732003/5000000), (732003/5000000), (4496179/50000000), (3646527/25000000), (3646527/25000000), (8197191/50000000), (4040231/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5510017/100000000), (1/100000000), (4231163/100000000), (2164887/50000000), (1/100000000), (5542053/100000000), (66907/25000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-1458530054191358846980499253941190164445362783/155958451168776781496567970852225000000000000000), (8839045958769587160277/14154721142050000000000), (-796300692858408842070731191277976702500754362783/77979225584388390748283985426112500000000000000), (8839045958769587160277/14154721142050000000000), (-1591142855662626325294481883302012214837063362783/155958451168776781496567970852225000000000000000)]
    bernstein := [(230199082208209280803185948225192492929956951592070337/1635342888927512824345452566043426816000000000000000000000), (29487802440095616150750462597502599349009038841978873/163534288892751282434545256604342681600000000000000000000), (524823044517576687132859917642647518970659767303361/2582120350938178143703346156910673920000000000000000000), (13708890579132468685285688587835180258129021118353/65413715557100512973818102641737072640000000000000000), (52139666079874425603873349269517701238813561777/261654862228402051895272410566948290560000000000000)]
    reserve := (4398907/31250000000) }

theorem tilt_030_017_valid : tilt_030_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_030_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_030_017]
  · intro i; fin_cases i <;> norm_num [tilt_030_017]
  · norm_num [tilt_030_017]
  · norm_num [tilt_030_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_030_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_030_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_030_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_030_017]

def tilt_030_018 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/320), (1/32)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(732003/5000000), (732003/5000000), (4496179/50000000), (3646527/25000000), (3646527/25000000), (8197191/50000000), (4040231/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5510017/100000000), (1/100000000), (4231163/100000000), (2164887/50000000), (1/100000000), (138689/2500000), (51923/20000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-70107584414545120840673701954113741544301483/7269084495756647508146044930380000000000000000), (8850462054351363973723/13730917278062500000000), (-38225210339107163984572032806583831182913101483/3634542247878323754073022465190000000000000000), (8850462054351363973723/13730917278062500000000), (-76380313093799782848303391911213548624281901483/7269084495756647508146044930380000000000000000)]
    bernstein := [(13129099201180743190367452554841048641928861105899637/76221875442225224175017472089181388800000000000000000000), (1631889525587212651783093433890427052276601574338573/7622187544222522417501747208918138880000000000000000000), (546134928786717051274187762274397338158941996598959/2286656263266756725250524162675441664000000000000000000), (751423748837312347487532264914346254859444459653/3048875017689008967000698883567255552000000000000000), (2889887130941198972014257685430284814358819877/12195500070756035868002795534269022208000000000000)]
    reserve := (4306211/25000000000) }

theorem tilt_030_018_valid : tilt_030_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_030_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_030_018]
  · intro i; fin_cases i <;> norm_num [tilt_030_018]
  · norm_num [tilt_030_018]
  · norm_num [tilt_030_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_030_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_030_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_030_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_030_018]

def tilt_030_019 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/320), (1/32)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(732003/5000000), (732003/5000000), (4496179/50000000), (3646527/25000000), (3646527/25000000), (8197191/50000000), (4040231/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5510017/100000000), (1/100000000), (4231163/100000000), (2164887/50000000), (1/100000000), (2772403/50000000), (263621/100000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-4341715513413666697447178733502169267470234267/461099131108206911293219926720637500000000000000), (16775479250669/26444768750000), (-2389027826680990992094373430601561005456855809767/230549565554103455646609963360318750000000000000), (16775479250669/26444768750000), (-4773713937848568317491299682469619841646241385267/461099131108206911293219926720637500000000000000)]
    bernstein := [(1142097207015884135848514302489809407853170965670533613/4834974825009191702161993778810191872000000000000000000000), (133875521191126257503663410838198242039665398141940677/483497482500919170216199377881019187200000000000000000000), (43617067989435733509951326385415257542429732399280791/145049244750275751064859813364305756160000000000000000000), (59500752279759299049949921190370937654587901006717/193398993000367668086479751152407674880000000000000000), (230332879520641842997509037070796809773831509533/773595972001470672345919004609630699520000000000000)]
    reserve := (944863/4000000000) }

theorem tilt_030_019_valid : tilt_030_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_030_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_030_019]
  · intro i; fin_cases i <;> norm_num [tilt_030_019]
  · norm_num [tilt_030_019]
  · norm_num [tilt_030_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_030_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_030_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_030_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_030_019]

def tilt_030_020 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(9/320), (1/32)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(732003/5000000), (732003/5000000), (4496179/50000000), (3646527/25000000), (3646527/25000000), (8197191/50000000), (4040231/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5510017/100000000), (1/100000000), (4231163/100000000), (2164887/50000000), (1/100000000), (2772403/50000000), (263621/100000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-4415156920747221776453056497635823720265984267/461099131108206911293219926720637500000000000000), (16775479250669/26444768750000), (-2388952232328038431819985618986674304072270559767/230549565554103455646609963360318750000000000000), (16775479250669/26444768750000), (-4773489307735329641863518181475712784424275135267/461099131108206911293219926720637500000000000000)]
    bernstein := [(373263729054418021442399882192754429036648561436783613/4834974825009191702161993778810191872000000000000000000000), (56999156546083009117392814798343158382088015698190677/483497482500919170216199377881019187200000000000000000000), (20556331495722366502075149998554915888745839734030791/145049244750275751064859813364305756160000000000000000000), (28756104841365925271648580080213830082824893016717/193398993000367668086479751152407674880000000000000000), (107366711086674213547759816725310441770785439533/773595972001470672345919004609630699520000000000000)]
    reserve := (77200759/1000000000000) }

theorem tilt_030_020_valid : tilt_030_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_030_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_030_020]
  · intro i; fin_cases i <;> norm_num [tilt_030_020]
  · norm_num [tilt_030_020]
  · norm_num [tilt_030_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_030_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_030_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_030_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_030_020]

def tiltBundle030_row : Alternative → Row
  | .zero => tilt_030_000
  | (.spike 0 false false) => tilt_030_001
  | (.spike 0 false true) => tilt_030_002
  | (.spike 0 true false) => tilt_030_003
  | (.spike 0 true true) => tilt_030_004
  | (.spike 1 false false) => tilt_030_005
  | (.spike 1 false true) => tilt_030_006
  | (.spike 1 true false) => tilt_030_007
  | (.spike 1 true true) => tilt_030_008
  | (.spike 2 false false) => tilt_030_009
  | (.spike 2 false true) => tilt_030_010
  | (.spike 2 true false) => tilt_030_011
  | (.spike 2 true true) => tilt_030_012
  | (.spike 3 false false) => tilt_030_013
  | (.spike 3 false true) => tilt_030_014
  | (.spike 3 true false) => tilt_030_015
  | (.spike 3 true true) => tilt_030_016
  | (.spike 4 false false) => tilt_030_017
  | (.spike 4 false true) => tilt_030_018
  | (.spike 4 true false) => tilt_030_019
  | (.spike 4 true true) => tilt_030_020

def tiltBundle030 : TiltBundle where
  interval := ⟨(9/320), (1/32)⟩
  lambda := ![(732003/5000000), (732003/5000000), (4496179/50000000), (3646527/25000000), (3646527/25000000), (8197191/50000000), (4040231/25000000)]
  row := tiltBundle030_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_030_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_030_001_valid | exact tilt_030_002_valid | exact tilt_030_003_valid | exact tilt_030_004_valid | exact tilt_030_005_valid | exact tilt_030_006_valid | exact tilt_030_007_valid | exact tilt_030_008_valid | exact tilt_030_009_valid | exact tilt_030_010_valid | exact tilt_030_011_valid | exact tilt_030_012_valid | exact tilt_030_013_valid | exact tilt_030_014_valid | exact tilt_030_015_valid | exact tilt_030_016_valid | exact tilt_030_017_valid | exact tilt_030_018_valid | exact tilt_030_019_valid | exact tilt_030_020_valid
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
