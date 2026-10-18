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

def tilt_018_000 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨0, (1/1280)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14478203/100000000), (14478203/100000000), (4240761/50000000), (1447761/10000000), (1447761/10000000), (8402569/50000000), (16801713/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2802141/50000000), (1/100000000), (2119951/50000000), (4239773/100000000), (1/100000000), (140121/2500000), (6691/100000000)]
    alternative := .zero
    polynomial := [(82629928371249266056163899947545686841449/262367574762784464717836339700000000000000000), (7802130304977/12470300000000), (-55396462946993721194433237955317186444313158551/131183787381392232358918169850000000000000000), (7802130304977/12470300000000), (-110793008523915813638132532074534320434313158551/262367574762784464717836339700000000000000000)]
    bernstein := [(82629928371249266056163899947545686841449/262367574762784464717836339700000000000000000), (229381773106405406224552512603584702979773/524735149525568929435672679400000000000000000), (665918204295245738961230470971645785678776966249/1289589103474038200981109176893440000000000000000000), (475140930826713584167252411566982454406763062973/859726068982692133987406117928960000000000000000000), (384536911727598405835822118212469235852367267904364649/704287595710621396162483091807404032000000000000000000000)]
    reserve := (314939559/1000000000000) }

theorem tilt_018_000_valid : tilt_018_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_018_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_018_000]
  · intro i; fin_cases i <;> norm_num [tilt_018_000]
  · norm_num [tilt_018_000]
  · norm_num [tilt_018_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_018_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_018_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_018_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_018_000]

def tilt_018_001 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨0, (1/1280)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14478203/100000000), (14478203/100000000), (4240761/50000000), (1447761/10000000), (1447761/10000000), (8402569/50000000), (16801713/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(7239/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4373/100000000), 0, 0]] i.1) i.2
    mu := ![(2802141/50000000), (1/100000000), (2119951/50000000), (4239773/100000000), (1/100000000), (140121/2500000), (11059/100000000)]
    alternative := (.spike 0 false false)
    polynomial := [(181028124035159222340282172978995404940049/433645644791755103170610085300000000000000000), (51064067894306993871/137909047700000000000), (-55435640690971561577270792536285898965284059951/216822822395877551585305042650000000000000000), (51064067894306993871/137909047700000000000), (-110871462410067158313763925354744776925973059951/433645644791755103170610085300000000000000000)]
    bernstein := [(181028124035159222340282172978995404940049/433645644791755103170610085300000000000000000), (3398223413704388694847593940990317878162659/6938330316668081650729761364800000000000000000), (1142643389431390242890135988181807191016524784849/2131455073280434683104182691266560000000000000000000), (6324890664343139633285512470573055091171114668259/11367760390828984976555641020088320000000000000000000), (641026705631718348265646490517209785629960694472943249/1164058664020888061599297640457043968000000000000000000000)]
    reserve := (20872817/50000000000) }

theorem tilt_018_001_valid : tilt_018_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_018_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_018_001]
  · intro i; fin_cases i <;> norm_num [tilt_018_001]
  · norm_num [tilt_018_001]
  · norm_num [tilt_018_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_018_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_018_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_018_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_018_001]

def tilt_018_002 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨0, (1/1280)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14478203/100000000), (14478203/100000000), (4240761/50000000), (1447761/10000000), (1447761/10000000), (8402569/50000000), (16801713/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (4289/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(129/50000000), 0, 0, (3417/100000000), 0]] i.1) i.2
    mu := ![(2802141/50000000), (941/25000000), (2119951/50000000), (4239773/100000000), (1/100000000), (140121/2500000), (3317/100000000)]
    alternative := (.spike 0 false true)
    polynomial := [(1309156529237651292554489572960490056925851/48956934628865931033949389543960000000000000000), (53383087315277531319/41363985100000000000), (-20839808096190379709501319594301749504272993274149/24478467314432965516974694771980000000000000000), (53383087315277531319/41363985100000000000), (-41679617501537288656653931743093071969036043474149/48956934628865931033949389543960000000000000000)]
    bernstein := [(1309156529237651292554489572960490056925851/48956934628865931033949389543960000000000000000), (109195618656000227586413052735748142393988683/391655477030927448271595116351680000000000000000), (106905001935793796315519212458370167141658357561051/240633125087801824218068039486472192000000000000000000), (335681185850768217012203714568055954976694138615883/641688333567471531248181438630592512000000000000000000), (67729313562737488642869568880346387873322614448027642651/131417770714618169599627558631545346457600000000000000000000)]
    reserve := (13370491/500000000000) }

theorem tilt_018_002_valid : tilt_018_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_018_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_018_002]
  · intro i; fin_cases i <;> norm_num [tilt_018_002]
  · norm_num [tilt_018_002]
  · norm_num [tilt_018_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_018_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_018_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_018_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_018_002]

def tilt_018_003 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨0, (1/1280)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14478203/100000000), (14478203/100000000), (4240761/50000000), (1447761/10000000), (1447761/10000000), (8402569/50000000), (16801713/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4373/100000000), 0, 0]] i.1) i.2
    mu := ![(5601511/100000000), (1/100000000), (2119951/50000000), (4239773/100000000), (1/100000000), (140121/2500000), (11059/100000000)]
    alternative := (.spike 0 true false)
    polynomial := [(3726128153578591038953039252855371410413977/7801762168509000895189344656700000000000000000), (51064067894306993871/137909047700000000000), (-997347687088374803292411403014752161328360586023/3900881084254500447594672328350000000000000000), (51064067894306993871/137909047700000000000), (-1994699100304903185175861759068757178028131586023/7801762168509000895189344656700000000000000000)]
    bernstein := [(3726128153578591038953039252855371410413977/7801762168509000895189344656700000000000000000), (68645506408122060946422492176480285932064257/124828194696144014323029514507200000000000000000), (22863786349592328767527589254580013958865139164377/38347221410655441200034666856611840000000000000000000), (126092411392902274112720469891360301024059514733057/204518514190162353066851556568596480000000000000000000), (12792365038824375926975769418095116297210055167753367577/20942695853072624954045599392624279552000000000000000000000)]
    reserve := (238800419/500000000000) }

theorem tilt_018_003_valid : tilt_018_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_018_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_018_003]
  · intro i; fin_cases i <;> norm_num [tilt_018_003]
  · norm_num [tilt_018_003]
  · norm_num [tilt_018_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_018_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_018_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_018_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_018_003]

def tilt_018_004 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨0, (1/1280)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14478203/100000000), (14478203/100000000), (4240761/50000000), (1447761/10000000), (1447761/10000000), (8402569/50000000), (16801713/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(129/50000000), 0, 0, (3417/100000000), 0]] i.1) i.2
    mu := ![(2803527/50000000), (1/100000000), (2119951/50000000), (4239773/100000000), (1/100000000), (140121/2500000), (3317/100000000)]
    alternative := (.spike 0 true true)
    polynomial := [(910813218108730285981221735170627494487/10844214885660861206111485275000000000000000), (53383087315277531319/41363985100000000000), (-4616124936954820043856573901555430210402380513/5422107442830430603055742637500000000000000), (53383087315277531319/41363985100000000000), (-9232250784722858196443433784332595591432255513/10844214885660861206111485275000000000000000)]
    bernstein := [(910813218108730285981221735170627494487/10844214885660861206111485275000000000000000), (233232174644379483856362650153553212644043/694029752682295117191135057600000000000000000), (26731507958773837574825828089319674990820121887/53301485006000265000279172423680000000000000000000), (659939587588758247994109409464001140823460695243/1137098346794672320005955678371840000000000000000000), (16668919363774282053832628523006789345150260293466087/29109717677943611392152465366319104000000000000000000000)]
    reserve := (83990701/1000000000000) }

theorem tilt_018_004_valid : tilt_018_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_018_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_018_004]
  · intro i; fin_cases i <;> norm_num [tilt_018_004]
  · norm_num [tilt_018_004]
  · norm_num [tilt_018_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_018_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_018_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_018_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_018_004]

def tilt_018_005 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨0, (1/1280)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14478203/100000000), (14478203/100000000), (4240761/50000000), (1447761/10000000), (1447761/10000000), (8402569/50000000), (16801713/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4373/100000000), 0, 0]] i.1) i.2
    mu := ![(2802141/50000000), (1/100000000), (2119951/50000000), (1059481/25000000), (1/100000000), (140121/2500000), (11059/100000000)]
    alternative := (.spike 1 false false)
    polynomial := [(8786390450978390733688940131833700692859/21672826417339489093510484820000000000000000), (51064067894306993871/137909047700000000000), (-2770573498593632930157034356737484891565907141/10836413208669744546755242410000000000000000), (51064067894306993871/137909047700000000000), (-5541155783577716838704802402415101616832507141/21672826417339489093510484820000000000000000)]
    bernstein := [(8786390450978390733688940131833700692859/21672826417339489093510484820000000000000000), (165659977296044262718240642940092106862619/346765222677431825496167757120000000000000000), (55824050207446975949702138129666099919286649659/106526276406507056792422734987264000000000000000000), (7542996629987630768823515446464855347639517859/13857076605724495192510274469888000000000000000000), (764306257011003993403925567624320341173593466900099/1418964644426188307713052105716531200000000000000000000)]
    reserve := (50676307/125000000000) }

theorem tilt_018_005_valid : tilt_018_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_018_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_018_005]
  · intro i; fin_cases i <;> norm_num [tilt_018_005]
  · norm_num [tilt_018_005]
  · norm_num [tilt_018_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_018_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_018_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_018_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_018_005]

def tilt_018_006 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨0, (1/1280)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14478203/100000000), (14478203/100000000), (4240761/50000000), (1447761/10000000), (1447761/10000000), (8402569/50000000), (16801713/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(129/50000000), 0, 0, (3417/100000000), 0]] i.1) i.2
    mu := ![(2802141/50000000), (1/100000000), (2119951/50000000), (2120811/50000000), (1/100000000), (140121/2500000), (3317/100000000)]
    alternative := (.spike 1 false true)
    polynomial := [(298267526431396960887790916632209238121/3098165904568572995858451300000000000000000), (53383087315277531319/41363985100000000000), (-1318815666147133035115327054604510848009261879/1549082952284286497929225650000000000000000), (53383087315277531319/41363985100000000000), (-2637631630561792501627614996999938328227761879/3098165904568572995858451300000000000000000)]
    bernstein := [(298267526431396960887790916632209238121/3098165904568572995858451300000000000000000), (17267273092926782219061055430773510925561/49570654473097167933735220800000000000000000), (7824152376231479618120115488632099417443077321/15228105054135449989243459829760000000000000000000), (48133254053225836442720699226139780287734067961/81216560288722399942631785758720000000000000000000), (4864410737899146572326484912876352518675710788890921/8316575773565173754125494861692928000000000000000000000)]
    reserve := (96272289/1000000000000) }

theorem tilt_018_006_valid : tilt_018_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_018_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_018_006]
  · intro i; fin_cases i <;> norm_num [tilt_018_006]
  · norm_num [tilt_018_006]
  · norm_num [tilt_018_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_018_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_018_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_018_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_018_006]

def tilt_018_007 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨0, (1/1280)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14478203/100000000), (14478203/100000000), (4240761/50000000), (1447761/10000000), (1447761/10000000), (8402569/50000000), (16801713/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4373/100000000), 0, 0]] i.1) i.2
    mu := ![(2802141/50000000), (1/100000000), (4238053/100000000), (4239773/100000000), (1/100000000), (140121/2500000), (11059/100000000)]
    alternative := (.spike 1 true false)
    polynomial := [(70291387469186690041147732786907540569091/173382613640280562169362743180000000000000000), (1736013392937159367821/4686862812700000000000), (-22164613401436297397398121216891462472922630909/86691306820140281084681371590000000000000000), (1736013392937159367821/4686862812700000000000), (-44329297094260063981486283581515711853385830909/173382613640280562169362743180000000000000000)]
    bernstein := [(70291387469186690041147732786907540569091/173382613640280562169362743180000000000000000), (1325352506255438971905337492431525717828581/2774121818244488994709803890880000000000000000), (446635738753358988050991897938829995155761452291/852210222564707019174851755278336000000000000000000), (2474445929669564489973349897564721586720589738981/4545121187011770768932542694817792000000000000000000), (250739024178265670143219527786954374556224332348517891/465420409550005326738692371949341900800000000000000000000)]
    reserve := (101352993/250000000000) }

theorem tilt_018_007_valid : tilt_018_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_018_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_018_007]
  · intro i; fin_cases i <;> norm_num [tilt_018_007]
  · norm_num [tilt_018_007]
  · norm_num [tilt_018_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_018_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_018_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_018_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_018_007]

def tilt_018_008 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨0, (1/1280)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14478203/100000000), (14478203/100000000), (4240761/50000000), (1447761/10000000), (1447761/10000000), (8402569/50000000), (16801713/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(129/50000000), 0, 0, (3417/100000000), 0]] i.1) i.2
    mu := ![(2802141/50000000), (1/100000000), (530219/12500000), (4239773/100000000), (1/100000000), (140121/2500000), (3317/100000000)]
    alternative := (.spike 1 true true)
    polynomial := [(782940114213259253224709791723461676141/8132687308923812908485254775000000000000000), (226954899318853618737/175873642300000000000), (-3461890716688601625196937394953924004880480109/4066343654461906454242627387500000000000000), (226954899318853618737/175873642300000000000), (-6923782216317317463653128014617639733222636359/8132687308923812908485254775000000000000000)]
    bernstein := [(782940114213259253224709791723461676141/8132687308923812908485254775000000000000000), (7882294713337032697220709974180549273963/22630086424831479397524187200000000000000000), (20536372797207455606094293233551961639607763091/39973784660822325207786724270080000000000000000000), (505334947101150297756407551801728912636297822749/852774072764209604432783451095040000000000000000000), (12766897437393000376909868858918178104937807389152441/21831016262763765873479256348033024000000000000000000000)]
    reserve := (3850831/40000000000) }

theorem tilt_018_008_valid : tilt_018_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_018_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_018_008]
  · intro i; fin_cases i <;> norm_num [tilt_018_008]
  · norm_num [tilt_018_008]
  · norm_num [tilt_018_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_018_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_018_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_018_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_018_008]

def tilt_018_009 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨0, (1/1280)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14478203/100000000), (14478203/100000000), (4240761/50000000), (1447761/10000000), (1447761/10000000), (8402569/50000000), (16801713/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4373/100000000), 0, 0]] i.1) i.2
    mu := ![(2802141/50000000), (1/100000000), (2119951/50000000), (169517/4000000), (1/100000000), (140121/2500000), (11059/100000000)]
    alternative := (.spike 2 false false)
    polynomial := [(7027705976291127534301350075245566616059/17338265225087274678189683700000000000000000), (51064067894306993871/137909047700000000000), (-2216459323288741650606635522361404971714383941/8669132612543637339094841850000000000000000), (51064067894306993871/137909047700000000000), (-4432925674283459592340805346072885188995383941/17338265225087274678189683700000000000000000)]
    bernstein := [(7027705976291127534301350075245566616059/17338265225087274678189683700000000000000000), (132505484418935090779849953954128166328819/277412243601396394851034939200000000000000000), (44652329889038828067935180297207931389458812859/85221041234348972498237933322240000000000000000000), (247373436815746422798083933520866270791047378419/454512219916527853323935644385280000000000000000000), (25065471453849628917108247545947242527848368865787259/46542051319452452180371009985052672000000000000000000000)]
    reserve := (202664623/500000000000) }

theorem tilt_018_009_valid : tilt_018_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_018_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_018_009]
  · intro i; fin_cases i <;> norm_num [tilt_018_009]
  · norm_num [tilt_018_009]
  · norm_num [tilt_018_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_018_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_018_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_018_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_018_009]

def tilt_018_010 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨0, (1/1280)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14478203/100000000), (14478203/100000000), (4240761/50000000), (1447761/10000000), (1447761/10000000), (8402569/50000000), (16801713/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(129/50000000), 0, 0, (3417/100000000), 0]] i.1) i.2
    mu := ![(2802141/50000000), (1/100000000), (2119951/50000000), (4241623/100000000), (1/100000000), (140121/2500000), (3317/100000000)]
    alternative := (.spike 2 false true)
    polynomial := [(20318970477579965743918293233928811543531/130122998669523663459240048900000000000000000), (53383087315277531319/41363985100000000000), (-55390263245192676862769255429045838809618956469/65061499334761831729620024450000000000000000), (53383087315277531319/41363985100000000000), (-110780546809355831305504254776384911548049456469/130122998669523663459240048900000000000000000)]
    bernstein := [(20318970477579965743918293233928811543531/130122998669523663459240048900000000000000000), (849893343506129155672853806897594097637121/2081967978712378615347840782400000000000000000), (366912403313572028758124928625429080279864614731/639580563060442710634856688353280000000000000000000), (2225852835493114553013863302656429367831708683521/3411096336322361123385902337884160000000000000000000), (225221094442103975659536220623827772690960626224284331/349296264839409779034716399399337984000000000000000000000)]
    reserve := (15615203/100000000000) }

theorem tilt_018_010_valid : tilt_018_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_018_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_018_010]
  · intro i; fin_cases i <;> norm_num [tilt_018_010]
  · norm_num [tilt_018_010]
  · norm_num [tilt_018_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_018_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_018_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_018_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_018_010]

def tilt_018_011 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨0, (1/1280)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14478203/100000000), (14478203/100000000), (4240761/50000000), (1447761/10000000), (1447761/10000000), (8402569/50000000), (16801713/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7239/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4373/100000000), 0, 0]] i.1) i.2
    mu := ![(2802141/50000000), (1/100000000), (2119951/50000000), (4239773/100000000), (1/100000000), (140121/2500000), (11059/100000000)]
    alternative := (.spike 2 true false)
    polynomial := [(181028003816661230833994308748687982434299/433645644791755103170610085300000000000000000), (51064067894306993871/137909047700000000000), (-55435640691091780075262298824150129272706565701/216822822395877551585305042650000000000000000), (51064067894306993871/137909047700000000000), (-110871462410187376811755431642609007233395565701/433645644791755103170610085300000000000000000)]
    bernstein := [(181028003816661230833994308748687982434299/433645644791755103170610085300000000000000000), (3398221490208420830746988113305399118070659/6938330316668081650729761364800000000000000000), (1142642798533308696540438371629135917608839879099/2131455073280434683104182691266560000000000000000000), (6324887512885422388775215781888256509717621776259/11367760390828984976555641020088320000000000000000000), (641026382922251136320464327702343368089211681488837499/1164058664020888061599297640457043968000000000000000000000)]
    reserve := (417456063/1000000000000) }

theorem tilt_018_011_valid : tilt_018_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_018_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_018_011]
  · intro i; fin_cases i <;> norm_num [tilt_018_011]
  · norm_num [tilt_018_011]
  · norm_num [tilt_018_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_018_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_018_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_018_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_018_011]

def tilt_018_012 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨0, (1/1280)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14478203/100000000), (14478203/100000000), (4240761/50000000), (1447761/10000000), (1447761/10000000), (8402569/50000000), (16801713/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (67/1562500), 0, 0], ![0, 0, 0, 0, 0], ![(129/50000000), 0, 0, (3417/100000000), 0]] i.1) i.2
    mu := ![(2802141/50000000), (1/100000000), (2119951/50000000), (4239773/100000000), (941/25000000), (140121/2500000), (3317/100000000)]
    alternative := (.spike 2 true true)
    polynomial := [(654708124918734288198172120551494009669813/24478467314432965516974694771980000000000000000), (53383087315277531319/41363985100000000000), (-10419904047965329554842017876223540680887515430187/12239233657216482758487347385990000000000000000), (53383087315277531319/41363985100000000000), (-20839808750638784028418323950619201913269040530187/24478467314432965516974694771980000000000000000)]
    bernstein := [(654708124918734288198172120551494009669813/24478467314432965516974694771980000000000000000), (109197696420798765857147890080888126093298883/391655477030927448271595116351680000000000000000), (53453139257372869414437990182539420634506253427413/120316562543900912109034019743236096000000000000000000), (335684590062691906913513942809170649409627669606083/641688333567471531248181438630592512000000000000000000), (33865005372882493412559570643952603716262102855755988213/65708885357309084799813779315772673228800000000000000000000)]
    reserve := (26746287/1000000000000) }

theorem tilt_018_012_valid : tilt_018_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_018_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_018_012]
  · intro i; fin_cases i <;> norm_num [tilt_018_012]
  · norm_num [tilt_018_012]
  · norm_num [tilt_018_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_018_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_018_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_018_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_018_012]

def tilt_018_013 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨0, (1/1280)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14478203/100000000), (14478203/100000000), (4240761/50000000), (1447761/10000000), (1447761/10000000), (8402569/50000000), (16801713/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4373/100000000), 0, 0]] i.1) i.2
    mu := ![(2802141/50000000), (1/100000000), (2119951/50000000), (4239773/100000000), (1/100000000), (5602069/100000000), (11059/100000000)]
    alternative := (.spike 3 false false)
    polynomial := [(74524714521456828916649328253107385218852293/156035251054846343314527360135300000000000000000), (51064067894306993871/137909047700000000000), (-19946954721998314981863956886234153469681970147707/78017625527423171657263680067650000000000000000), (51064067894306993871/137909047700000000000), (-39893983968711151420556830421796560046749159147707/156035251054846343314527360135300000000000000000)]
    bernstein := [(74524714521456828916649328253107385218852293/156035251054846343314527360135300000000000000000), (1372944560252565145431533470781647262280446063/2496564016877541493032437762164800000000000000000), (457286306281313104880155429332336504647721300405893/766944465984780746659564880537026560000000000000000000), (2521904654848007280465908469433908421812872646065263/4090370485252163982184346029530808320000000000000000000), (255853078786074174709893903491267963869944528240160634693/418853937689821591775677033423954771968000000000000000000000)]
    reserve := (477614603/1000000000000) }

theorem tilt_018_013_valid : tilt_018_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_018_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_018_013]
  · intro i; fin_cases i <;> norm_num [tilt_018_013]
  · norm_num [tilt_018_013]
  · norm_num [tilt_018_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_018_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_018_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_018_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_018_013]

def tilt_018_014 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨0, (1/1280)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14478203/100000000), (14478203/100000000), (4240761/50000000), (1447761/10000000), (1447761/10000000), (8402569/50000000), (16801713/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(129/50000000), 0, 0, (3417/100000000), 0]] i.1) i.2
    mu := ![(2802141/50000000), (1/100000000), (2119951/50000000), (4239773/100000000), (1/100000000), (1401903/25000000), (3317/100000000)]
    alternative := (.spike 3 false true)
    polynomial := [(109271999902635577991212608954128018070661/1301305722230823322539769067700000000000000000), (53383087315277531319/41363985100000000000), (-553934965196241260468096470569496185313418429339/650652861115411661269884533850000000000000000), (53383087315277531319/41363985100000000000), (-1107870039664482423571770932351601324754854929339/1301305722230823322539769067700000000000000000)]
    bernstein := [(109271999902635577991212608954128018070661/1301305722230823322539769067700000000000000000), (6996555600695419858935063953225424788858701/20820891555693173160636305083200000000000000000), (3207655061949590307919198606760874770540454517861/6396177885908942794947472921559040000000000000000000), (19797516065106569585013006257109691882737020577101/34112948724847694906386522248314880000000000000000000), (2000201556937306714112050506414726554306529058091195461/3493165949424403958413979878227443712000000000000000000000)]
    reserve := (83971043/1000000000000) }

theorem tilt_018_014_valid : tilt_018_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_018_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_018_014]
  · intro i; fin_cases i <;> norm_num [tilt_018_014]
  · norm_num [tilt_018_014]
  · norm_num [tilt_018_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_018_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_018_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_018_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_018_014]

def tilt_018_015 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨0, (1/1280)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14478203/100000000), (14478203/100000000), (4240761/50000000), (1447761/10000000), (1447761/10000000), (8402569/50000000), (16801713/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7239/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4373/100000000), 0, 0]] i.1) i.2
    mu := ![(2802141/50000000), (1/100000000), (2119951/50000000), (4239773/100000000), (1/100000000), (140121/2500000), (11059/100000000)]
    alternative := (.spike 3 true false)
    polynomial := [(181028003816661230833994308748687982434299/433645644791755103170610085300000000000000000), (51064067894306993871/137909047700000000000), (-55435640691091780075262298824150129272706565701/216822822395877551585305042650000000000000000), (51064067894306993871/137909047700000000000), (-110871462410187376811755431642609007233395565701/433645644791755103170610085300000000000000000)]
    bernstein := [(181028003816661230833994308748687982434299/433645644791755103170610085300000000000000000), (3398221490208420830746988113305399118070659/6938330316668081650729761364800000000000000000), (1142642798533308696540438371629135917608839879099/2131455073280434683104182691266560000000000000000000), (6324887512885422388775215781888256509717621776259/11367760390828984976555641020088320000000000000000000), (641026382922251136320464327702343368089211681488837499/1164058664020888061599297640457043968000000000000000000000)]
    reserve := (417456063/1000000000000) }

theorem tilt_018_015_valid : tilt_018_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_018_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_018_015]
  · intro i; fin_cases i <;> norm_num [tilt_018_015]
  · norm_num [tilt_018_015]
  · norm_num [tilt_018_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_018_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_018_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_018_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_018_015]

def tilt_018_016 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨0, (1/1280)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14478203/100000000), (14478203/100000000), (4240761/50000000), (1447761/10000000), (1447761/10000000), (8402569/50000000), (16801713/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (67/1562500), 0, 0], ![0, 0, 0, 0, 0], ![(129/50000000), 0, 0, (3417/100000000), 0]] i.1) i.2
    mu := ![(2802141/50000000), (1/100000000), (2119951/50000000), (4239773/100000000), (941/25000000), (140121/2500000), (3317/100000000)]
    alternative := (.spike 3 true true)
    polynomial := [(654708124918734288198172120551494009669813/24478467314432965516974694771980000000000000000), (53383087315277531319/41363985100000000000), (-10419904047965329554842017876223540680887515430187/12239233657216482758487347385990000000000000000), (53383087315277531319/41363985100000000000), (-20839808750638784028418323950619201913269040530187/24478467314432965516974694771980000000000000000)]
    bernstein := [(654708124918734288198172120551494009669813/24478467314432965516974694771980000000000000000), (109197696420798765857147890080888126093298883/391655477030927448271595116351680000000000000000), (53453139257372869414437990182539420634506253427413/120316562543900912109034019743236096000000000000000000), (335684590062691906913513942809170649409627669606083/641688333567471531248181438630592512000000000000000000), (33865005372882493412559570643952603716262102855755988213/65708885357309084799813779315772673228800000000000000000000)]
    reserve := (26746287/1000000000000) }

theorem tilt_018_016_valid : tilt_018_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_018_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_018_016]
  · intro i; fin_cases i <;> norm_num [tilt_018_016]
  · norm_num [tilt_018_016]
  · norm_num [tilt_018_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_018_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_018_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_018_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_018_016]

def tilt_018_017 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨0, (1/1280)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14478203/100000000), (14478203/100000000), (4240761/50000000), (1447761/10000000), (1447761/10000000), (8402569/50000000), (16801713/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4373/100000000), 0, 0]] i.1) i.2
    mu := ![(2802141/50000000), (1/100000000), (2119951/50000000), (4239773/100000000), (1/100000000), (5602069/100000000), (11059/100000000)]
    alternative := (.spike 4 false false)
    polynomial := [(74519644449892397903015217629029942533420293/156035251054846343314527360135300000000000000000), (51064067894306993871/137909047700000000000), (-19946954727068386546294970520344777547124655579707/78017625527423171657263680067650000000000000000), (51064067894306993871/137909047700000000000), (-39893983973781222984987844055907184124191844579707/156035251054846343314527360135300000000000000000)]
    bernstein := [(74519644449892397903015217629029942533420293/156035251054846343314527360135300000000000000000), (1372863439107534249213387700796408179313534063/2496564016877541493032437762164800000000000000000), (457261385860489541997510035158760434282843248573893/766944465984780746659564880537026560000000000000000000), (2521771745882867515071202221744322723040801058353263/4090370485252163982184346029530808320000000000000000000), (255839468899737052412240646558713907716578224403977602693/418853937689821591775677033423954771968000000000000000000000)]
    reserve := (47758211/100000000000) }

theorem tilt_018_017_valid : tilt_018_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_018_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_018_017]
  · intro i; fin_cases i <;> norm_num [tilt_018_017]
  · norm_num [tilt_018_017]
  · norm_num [tilt_018_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_018_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_018_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_018_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_018_017]

def tilt_018_018 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨0, (1/1280)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14478203/100000000), (14478203/100000000), (4240761/50000000), (1447761/10000000), (1447761/10000000), (8402569/50000000), (16801713/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(129/50000000), 0, 0, (3417/100000000), 0]] i.1) i.2
    mu := ![(2802141/50000000), (1/100000000), (2119951/50000000), (4239773/100000000), (1/100000000), (1401903/25000000), (3317/100000000)]
    alternative := (.spike 4 false true)
    polynomial := [(139518013271223889906477979662933975764661/1301305722230823322539769067700000000000000000), (53383087315277531319/41363985100000000000), (-553934934950227891879784555304125476507460735339/650652861115411661269884533850000000000000000), (53383087315277531319/41363985100000000000), (-1107870009418469054983459017086230615948897235339/1301305722230823322539769067700000000000000000)]
    bernstein := [(139518013271223889906477979662933975764661/1301305722230823322539769067700000000000000000), (7480491814592832849579309884566320111962701/20820891555693173160636305083200000000000000000), (3356320297104888947233422872134168522603961011861/6396177885908942794947472921559040000000000000000000), (20590397641892304926297529435264546121005937281101/34112948724847694906386522248314880000000000000000000), (2081392679955264562168044510140482262983656020388089461/3493165949424403958413979878227443712000000000000000000000)]
    reserve := (53606931/500000000000) }

theorem tilt_018_018_valid : tilt_018_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_018_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_018_018]
  · intro i; fin_cases i <;> norm_num [tilt_018_018]
  · norm_num [tilt_018_018]
  · norm_num [tilt_018_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_018_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_018_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_018_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_018_018]

def tilt_018_019 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨0, (1/1280)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14478203/100000000), (14478203/100000000), (4240761/50000000), (1447761/10000000), (1447761/10000000), (8402569/50000000), (16801713/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2802141/50000000), (1/100000000), (2119951/50000000), (4239773/100000000), (1/100000000), (140121/2500000), (6691/100000000)]
    alternative := (.spike 4 true false)
    polynomial := [(126712174137999211128476131615418431747699/262367574762784464717836339700000000000000000), (7802130304977/12470300000000), (-55396518305554337989724476565189521418227651301/131183787381392232358918169850000000000000000), (7802130304977/12470300000000), (-110793163323282813978660081606510658254887050301/262367574762784464717836339700000000000000000)]
    bernstein := [(126712174137999211128476131615418431747699/262367574762784464717836339700000000000000000), (317546264639905296369176975939330192792273/524735149525568929435672679400000000000000000), (882591203329414452185368313455701566468062473499/1289589103474038200981109176893440000000000000000000), (619589523038078570589622655076523194967734077473/859726068982692133987406117928960000000000000000000), (502869107767528088788622315829520644922315397487272899/704287595710621396162483091807404032000000000000000000000)]
    reserve := (120739171/250000000000) }

theorem tilt_018_019_valid : tilt_018_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_018_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_018_019]
  · intro i; fin_cases i <;> norm_num [tilt_018_019]
  · norm_num [tilt_018_019]
  · norm_num [tilt_018_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_018_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_018_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_018_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_018_019]

def tilt_018_020 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨0, (1/1280)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14478203/100000000), (14478203/100000000), (4240761/50000000), (1447761/10000000), (1447761/10000000), (8402569/50000000), (16801713/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3/25000000), 0, 0]] i.1) i.2
    mu := ![(2802141/50000000), (1/100000000), (2119951/50000000), (4239773/100000000), (1/100000000), (140121/2500000), (6691/100000000)]
    alternative := (.spike 4 true true)
    polynomial := [(82646583180350789105604552530474095747699/262367574762784464717836339700000000000000000), (13051019753322325467/20859694325000000000), (-55396513736390141086500401205994178590441651301/131183787381392232358918169850000000000000000), (13051019753322325467/20859694325000000000), (-110793110119363462523789908016540887654979050301/262367574762784464717836339700000000000000000)]
    bernstein := [(82646583180350789105604552530474095747699/262367574762784464717836339700000000000000000), (458830227214433590358284889794303017250171/1049470299051137858871345358800000000000000000), (666000167017741651966153047354698641184488473499/1289589103474038200981109176893440000000000000000000), (950391111041224049048494230432231080648667820571/1719452137965384267974812235857920000000000000000000), (384581618513402480395106293334879967055600636755272899/704287595710621396162483091807404032000000000000000000000)]
    reserve := (157501519/500000000000) }

theorem tilt_018_020_valid : tilt_018_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_018_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_018_020]
  · intro i; fin_cases i <;> norm_num [tilt_018_020]
  · norm_num [tilt_018_020]
  · norm_num [tilt_018_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_018_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_018_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_018_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_018_020]

def tiltBundle018_row : Alternative → Row
  | .zero => tilt_018_000
  | (.spike 0 false false) => tilt_018_001
  | (.spike 0 false true) => tilt_018_002
  | (.spike 0 true false) => tilt_018_003
  | (.spike 0 true true) => tilt_018_004
  | (.spike 1 false false) => tilt_018_005
  | (.spike 1 false true) => tilt_018_006
  | (.spike 1 true false) => tilt_018_007
  | (.spike 1 true true) => tilt_018_008
  | (.spike 2 false false) => tilt_018_009
  | (.spike 2 false true) => tilt_018_010
  | (.spike 2 true false) => tilt_018_011
  | (.spike 2 true true) => tilt_018_012
  | (.spike 3 false false) => tilt_018_013
  | (.spike 3 false true) => tilt_018_014
  | (.spike 3 true false) => tilt_018_015
  | (.spike 3 true true) => tilt_018_016
  | (.spike 4 false false) => tilt_018_017
  | (.spike 4 false true) => tilt_018_018
  | (.spike 4 true false) => tilt_018_019
  | (.spike 4 true true) => tilt_018_020

def tiltBundle018 : TiltBundle where
  interval := ⟨0, (1/1280)⟩
  lambda := ![(14478203/100000000), (14478203/100000000), (4240761/50000000), (1447761/10000000), (1447761/10000000), (8402569/50000000), (16801713/100000000)]
  row := tiltBundle018_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_018_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_018_001_valid | exact tilt_018_002_valid | exact tilt_018_003_valid | exact tilt_018_004_valid | exact tilt_018_005_valid | exact tilt_018_006_valid | exact tilt_018_007_valid | exact tilt_018_008_valid | exact tilt_018_009_valid | exact tilt_018_010_valid | exact tilt_018_011_valid | exact tilt_018_012_valid | exact tilt_018_013_valid | exact tilt_018_014_valid | exact tilt_018_015_valid | exact tilt_018_016_valid | exact tilt_018_017_valid | exact tilt_018_018_valid | exact tilt_018_019_valid | exact tilt_018_020_valid
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
