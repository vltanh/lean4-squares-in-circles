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

def tilt_035_000 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/160), (29/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14723183/100000000), (14723183/100000000), (9252921/100000000), (7317651/50000000), (7317651/50000000), (16180483/100000000), (3962407/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(4373/80000), (1/100000000), (1054387/25000000), (4375187/100000000), (1/100000000), (2756437/50000000), (375757/100000000)]
    alternative := .zero
    polynomial := [(-29906291581503488175250799305511301312974911/2089446668887171343404633633300000000000000000), (269925582911831/421754800000000), (-7467789560144543371799311603275736018312974911/1044723334443585671702316816650000000000000000), (269925582911831/421754800000000), (-14905672828707583255423372407245960735312974911/2089446668887171343404633633300000000000000000)]
    bernstein := [(44892711102566366004609755360073898789564417561889/1369339768921896611613660697919488000000000000000000000), (213445895264589511567485535592039291195990215801883/5477359075687586446454642791677952000000000000000000000), (2776731400738180018344763601124045659829949971241003/65728308908251037357455713500135424000000000000000000000), (3734605291439173266352056233063470077274535059610147/87637745211001383143274284666847232000000000000000000000), (14047880079210108231113408809056793331918430910513809/350550980844005532573097138667388928000000000000000000000)]
    reserve := (32784201/1000000000000) }

theorem tilt_035_000_valid : tilt_035_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_035_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_035_000]
  · intro i; fin_cases i <;> norm_num [tilt_035_000]
  · norm_num [tilt_035_000]
  · norm_num [tilt_035_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_035_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_035_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_035_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_035_000]

def tilt_035_001 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/160), (29/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14723183/100000000), (14723183/100000000), (9252921/100000000), (7317651/50000000), (7317651/50000000), (16180483/100000000), (3962407/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(14723/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(4373/80000), (1/100000000), (1054387/25000000), (4375187/100000000), (1/100000000), (2756437/50000000), (379699/100000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-89586139546000041863600497764619676445848809/6334100049205657421573484879300000000000000000), (12676108020894528712931/20017484475650000000000), (-22413921847934718693684334436101043428449848809/3167050024602828710786742439650000000000000000), (12676108020894528712931/20017484475650000000000), (-44738257556323437345505068374437467180453848809/6334100049205657421573484879300000000000000000)]
    bernstein := [(175184629373948290697838386265540361119198310750391/4151115808247419647802399050498048000000000000000000000), (266583272595366587120487401360256318609984942095759/5534821077663226197069865400664064000000000000000000000), (10211499108552511888771317350965436897426211829590557/199253558795876143094515154423906304000000000000000000000), (4556556245272221179583524527995410620620169215885431/88557137242611619153117846410625024000000000000000000000), (51835371794639456345777373968515874880615831339196871/1062685646911339429837414156927500288000000000000000000000)]
    reserve := (5275227/125000000000) }

theorem tilt_035_001_valid : tilt_035_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_035_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_035_001]
  · intro i; fin_cases i <;> norm_num [tilt_035_001]
  · norm_num [tilt_035_001]
  · norm_num [tilt_035_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_035_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_035_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_035_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_035_001]

def tilt_035_002 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/160), (29/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14723183/100000000), (14723183/100000000), (9252921/100000000), (7317651/50000000), (7317651/50000000), (16180483/100000000), (3962407/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (4361/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(4373/80000), (957/25000000), (1054387/25000000), (4375187/100000000), (1/100000000), (2756437/50000000), (371817/100000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-19071891330765458039686901592043332668351581277/1319089101069644597852479829777400000000000000000), (12680566275051419511569/19601950558950000000000), (-1587391452679002335010027403780496860182093193759/219848183511607432975413304962900000000000000000), (12680566275051419511569/19601950558950000000000), (-9505276824743248552020477521090937828424207581277/1319089101069644597852479829777400000000000000000)]
    bernstein := [(44189736458398924103032110267080715613325807034896323/864478233277002283648601181242916864000000000000000000000), (198937361602285692384552054107420764574838356614368881/3457912933108009134594404724971667456000000000000000000000), (843837990654103482512266835991903815904665136104896907/13831651732432036538377618899886669824000000000000000000000), (3405173260262371896117156482235820348572752165669352329/55326606929728146153510475599546679296000000000000000000000), (13089707592962203953517441063199890693525565852776927763/221306427718912584614041902398186717184000000000000000000000)]
    reserve := (25558617/500000000000) }

theorem tilt_035_002_valid : tilt_035_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_035_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_035_002]
  · intro i; fin_cases i <;> norm_num [tilt_035_002]
  · norm_num [tilt_035_002]
  · norm_num [tilt_035_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_035_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_035_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_035_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_035_002]

def tilt_035_003 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/160), (29/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14723183/100000000), (14723183/100000000), (9252921/100000000), (7317651/50000000), (7317651/50000000), (16180483/100000000), (3962407/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(218541/4000000), (1/100000000), (1054387/25000000), (4375187/100000000), (1/100000000), (2756437/50000000), (379699/100000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-1486669904433330724253190132498966408070437181/105515706902466161945886954722700000000000000000), (12676108020894528712931/20017484475650000000000), (-373373448625904400385626390499751072756626437181/52757853451233080972943477361350000000000000000), (12676108020894528712931/20017484475650000000000), (-745260227347375470046999590867003179105182437181/105515706902466161945886954722700000000000000000)]
    bernstein := [(6660318567204964176208619106814146826878598668475619/69150773675600223892856474647068672000000000000000000000), (9430553740768949062119737718206787782553403931704731/92201031567466965190475299529424896000000000000000000000), (349748918829822456360303576759867363157474477025811713/3319237136428810746857110783059296256000000000000000000000), (155751260282842951899056084443591151116836838787714979/1475216505079471443047604792470798336000000000000000000000), (1821718065467997790848059626215420194885898852221381939/17702598060953657316571257509649580032000000000000000000000)]
    reserve := (96315893/1000000000000) }

theorem tilt_035_003_valid : tilt_035_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_035_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_035_003]
  · intro i; fin_cases i <;> norm_num [tilt_035_003]
  · norm_num [tilt_035_003]
  · norm_num [tilt_035_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_035_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_035_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_035_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_035_003]

def tilt_035_004 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/160), (29/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14723183/100000000), (14723183/100000000), (9252921/100000000), (7317651/50000000), (7317651/50000000), (16180483/100000000), (3962407/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(341811/6250000), (1/100000000), (1054387/25000000), (4375187/100000000), (1/100000000), (2756437/50000000), (371817/100000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-413510280780902697969796446167663330356678429/28730122915567833783018383084640000000000000000), (12680566275051419511569/19601950558950000000000), (-34573194907308523850628804237418101575605826143/4788353819261305630503063847440000000000000000), (12680566275051419511569/19601950558950000000000), (-207025659163070240405803028978340946123278278429/28730122915567833783018383084640000000000000000)]
    bernstein := [(2199756247317375341294939790944355803874288445376771/18828573353946535548038927538349670400000000000000000000), (9282414651725322730485008146856323263890184301529137/75314293415786142192155710153398681600000000000000000000), (38178407151952527014462097110419885810305388349300939/301257173663144568768622840613594726400000000000000000000), (153368676613752287696005012441426524308829416906377033/1205028694652578275074491362454378905600000000000000000000), (601932083735369378310135969772950042575076604865869651/4820114778610313100297965449817515622400000000000000000000)]
    reserve := (14603843/125000000000) }

theorem tilt_035_004_valid : tilt_035_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_035_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_035_004]
  · intro i; fin_cases i <;> norm_num [tilt_035_004]
  · norm_num [tilt_035_004]
  · norm_num [tilt_035_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_035_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_035_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_035_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_035_004]

def tilt_035_005 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/160), (29/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14723183/100000000), (14723183/100000000), (9252921/100000000), (7317651/50000000), (7317651/50000000), (16180483/100000000), (3962407/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(4373/80000), (1/100000000), (1054387/25000000), (4373211/100000000), (1/100000000), (2756437/50000000), (379699/100000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-398114588753714840856963183678662010349253/28138841466445228307581724324000000000000000), (12676108020894528712931/20017484475650000000000), (-99572573227251362480753501637368293565069253/14069420733222614153790862162000000000000000), (12676108020894528712931/20017484475650000000000), (-198747031865749010120650040091057925119789253/28138841466445228307581724324000000000000000)]
    bernstein := [(690228178816999057895571862221316659803306797147/18441071143449544823656758852976640000000000000000000), (3200740173860828615268400471314707906868118137209/73764284573798179294627035411906560000000000000000000), (13712824591329001949586257962730880704652494644323/295057138295192717178508141647626240000000000000000000), (55092291724570390606428571303478524077856532038481/1180228553180770868714032566590504960000000000000000000), (207736378809730563481010379711359905789731610027307/4720914212723083474856130266362019840000000000000000000)]
    reserve := (7485771/200000000000) }

theorem tilt_035_005_valid : tilt_035_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_035_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_035_005]
  · intro i; fin_cases i <;> norm_num [tilt_035_005]
  · norm_num [tilt_035_005]
  · norm_num [tilt_035_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_035_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_035_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_035_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_035_005]

def tilt_035_006 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/160), (29/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14723183/100000000), (14723183/100000000), (9252921/100000000), (7317651/50000000), (7317651/50000000), (16180483/100000000), (3962407/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(4373/80000), (1/100000000), (1054387/25000000), (4377163/100000000), (1/100000000), (2756437/50000000), (371817/100000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-5952603453334334247263973194793441542393869/413694310852704400760488563540000000000000000), (12680566275051419511569/19601950558950000000000), (-497830035137778067703614852112456036837064623/68949051808784066793414760590000000000000000), (12680566275051419511569/19601950558950000000000), (-2981027607373334071974425139479942779479993869/413694310852704400760488563540000000000000000)]
    bernstein := [(32770037349053281008534995392321669089483112333331/271118703560428356082393785001574400000000000000000000), (138040931984309807283101685022673600743045014111457/1084474814241713424329575140006297600000000000000000000), (81038029479282439778397368906569950748942609929997/619699893852407671045471508575027200000000000000000000), (2278501968967415386448753085159557842691709338145913/17351597027867414789273202240100761600000000000000000000), (8947821738998910005052018028282873603146982912583011/69406388111469659157092808960403046400000000000000000000)]
    reserve := (120869703/1000000000000) }

theorem tilt_035_006_valid : tilt_035_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_035_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_035_006]
  · intro i; fin_cases i <;> norm_num [tilt_035_006]
  · norm_num [tilt_035_006]
  · norm_num [tilt_035_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_035_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_035_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_035_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_035_006]

def tilt_035_007 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/160), (29/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14723183/100000000), (14723183/100000000), (9252921/100000000), (7317651/50000000), (7317651/50000000), (16180483/100000000), (3962407/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(4373/80000), (1/100000000), (2107747/50000000), (4375187/100000000), (1/100000000), (2756437/50000000), (379699/100000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-29857793810966266215508300315433478340440823/2110338420398626060031286430550000000000000000), (6336541788742382220809/10003867851912500000000), (-7468019950472709918462192330653545835089315823/1055169210199313030015643215275000000000000000), (6336541788742382220809/10003867851912500000000), (-14906182107134453570708876360991658191838190823/2110338420398626060031286430550000000000000000)]
    bernstein := [(60280899866144385334810247696343217301011365811577/1383031387192443574702103875125248000000000000000000000), (274390171318789695299114895329216858922223728312419/5532125548769774298808415500500992000000000000000000000), (3500754067577650131260960242543780210551998981422579/66385506585237291585700986006011904000000000000000000000), (4690214763476792491861582622245980259931966791299371/88514008780316388780934648008015872000000000000000000000), (17831264638838967885843013279674008684619674217292137/354056035121265555123738592032063488000000000000000000000)]
    reserve := (43586067/1000000000000) }

theorem tilt_035_007_valid : tilt_035_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_035_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_035_007]
  · intro i; fin_cases i <;> norm_num [tilt_035_007]
  · norm_num [tilt_035_007]
  · norm_num [tilt_035_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_035_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_035_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_035_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_035_007]

def tilt_035_008 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/160), (29/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14723183/100000000), (14723183/100000000), (9252921/100000000), (7317651/50000000), (7317651/50000000), (16180483/100000000), (3962407/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(4373/80000), (1/100000000), (4219603/100000000), (4375187/100000000), (1/100000000), (2756437/50000000), (371817/100000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-119055284538073083643729755487201143117242719/8274180734494572753225374573700000000000000000), (25367319526737557917093/39223003216275000000000), (-9956509549107146795022223828727630971594247573/1379030122415762125537562428950000000000000000), (25367319526737557917093/39223003216275000000000), (-59620002010104807686489613216878584686448242719/8274180734494572753225374573700000000000000000)]
    bernstein := [(622062388729228368519319248937182060591144831964481/5422567086158363199553781480620032000000000000000000000), (2626370099541690511142126821744233961076392405360507/21690268344633452798215125922480128000000000000000000000), (10803151276246822747974020044545810719202449069690329/86761073378533811192860503689920512000000000000000000000), (43383840127341315481639873907988625541043880047007363/347044293514135244771442014759682048000000000000000000000), (170141633865754362307363110400412249258905662402986161/1388177174056540979085768059038728192000000000000000000000)]
    reserve := (28679331/250000000000) }

theorem tilt_035_008_valid : tilt_035_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_035_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_035_008]
  · intro i; fin_cases i <;> norm_num [tilt_035_008]
  · norm_num [tilt_035_008]
  · norm_num [tilt_035_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_035_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_035_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_035_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_035_008]

def tilt_035_009 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/160), (29/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14723183/100000000), (14723183/100000000), (9252921/100000000), (7317651/50000000), (7317651/50000000), (16180483/100000000), (3962407/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(4373/80000), (1/100000000), (1054387/25000000), (1093303/25000000), (1/100000000), (2756437/50000000), (379699/100000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-7464689025827490311428491045227748276546257/527603398140216092552429243900000000000000000), (12676108020894528712931/20017484475650000000000), (-1866986213704925874616035652368467729968546257/263801699070108046276214621950000000000000000), (12676108020894528712931/20017484475650000000000), (-3726507738384024258920642813691707711660546257/527603398140216092552429243900000000000000000)]
    bernstein := [(12916269203825524202254998742866825247138871355343/345770163005172018415160029282304000000000000000000000), (59911836587023443617976813287507137854730108800821/1383080652020688073660640117129216000000000000000000000), (256707270113580424148809330704310968543080127228087/5532322608082752294642560468516864000000000000000000000), (1031347592908509236451605173791946518969469887215789/22129290432331009178570241874067456000000000000000000000), (3888525079223356051340512635842397659211471107052383/88517161729324036714280967496269824000000000000000000000)]
    reserve := (37355071/1000000000000) }

theorem tilt_035_009_valid : tilt_035_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_035_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_035_009]
  · intro i; fin_cases i <;> norm_num [tilt_035_009]
  · norm_num [tilt_035_009]
  · norm_num [tilt_035_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_035_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_035_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_035_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_035_009]

def tilt_035_010 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/160), (29/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14723183/100000000), (14723183/100000000), (9252921/100000000), (7317651/50000000), (7317651/50000000), (16180483/100000000), (3962407/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(4373/80000), (1/100000000), (1054387/25000000), (1094291/25000000), (1/100000000), (2756437/50000000), (371817/100000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-7412960730006737562047094302874897941564947/517118006705846631040009008900000000000000000), (12680566275051419511569/19601950558950000000000), (-622278420993566652182420824095303334016521649/86186334450974438506668168150000000000000000), (12680566275051419511569/19601950558950000000000), (-3726257565231393175532477850268945106157564947/517118006705846631040009008900000000000000000)]
    bernstein := [(59248274598944879104809871221309597712370521608653/338898456874743648118380304072704000000000000000000000), (245699069067848287781502749030109876313869043155391/1355593827498974592473521216290816000000000000000000000), (1001694578951384076536064979672756060110407804607877/5422375309995898369894084865163264000000000000000000000), (4018656503702967282484998832838399140425036183834919/21689501239983593479576339460653056000000000000000000000), (15867224137696312562137944463404825529239945057402493/86758004959934373918305357842612224000000000000000000000)]
    reserve := (87413019/500000000000) }

theorem tilt_035_010_valid : tilt_035_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_035_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_035_010]
  · intro i; fin_cases i <;> norm_num [tilt_035_010]
  · norm_num [tilt_035_010]
  · norm_num [tilt_035_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_035_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_035_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_035_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_035_010]

def tilt_035_011 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/160), (29/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14723183/100000000), (14723183/100000000), (9252921/100000000), (7317651/50000000), (7317651/50000000), (16180483/100000000), (3962407/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(2927/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(4373/80000), (1/100000000), (1054387/25000000), (4375187/100000000), (1/100000000), (2756437/50000000), (379699/100000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-89592178968645078773437026368822141967847559/6334100049205657421573484879300000000000000000), (12676108020894528712931/20017484475650000000000), (-22413927887357363730594170964705245893971847559/3167050024602828710786742439650000000000000000), (12676108020894528712931/20017484475650000000000), (-44738263595746082382414904903041669645975847559/6334100049205657421573484879300000000000000000)]
    bernstein := [(171211467145111262134352599748010721000788727751641/4151115808247419647802399050498048000000000000000000000), (261285361511563896415205426051822024029700090907009/5534821077663226197069865400664064000000000000000000000), (10020761142005880687273015320497618012449567626124307/199253558795876143094515154423906304000000000000000000000), (4471777894336626802579873733517299181506492479686681/88557137242611619153117846410625024000000000000000000000), (50817959697438898125498568210310251150863584525298121/1062685646911339429837414156927500288000000000000000000000)]
    reserve := (8248937/200000000000) }

theorem tilt_035_011_valid : tilt_035_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_035_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_035_011]
  · intro i; fin_cases i <;> norm_num [tilt_035_011]
  · norm_num [tilt_035_011]
  · norm_num [tilt_035_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_035_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_035_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_035_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_035_011]

def tilt_035_012 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/160), (29/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14723183/100000000), (14723183/100000000), (9252921/100000000), (7317651/50000000), (7317651/50000000), (16180483/100000000), (3962407/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (867/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(4373/80000), (1/100000000), (1054387/25000000), (4375187/100000000), (761/20000000), (2756437/50000000), (371817/100000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-22747523166146112537624270018222408535002623147/1573396247514105860447863872195300000000000000000), (12680566275051419511569/19601950558950000000000), (-1893424188580695421660760248166643287502839541049/262232707919017643407977312032550000000000000000), (12680566275051419511569/19601950558950000000000), (-11337797608318026417426937218981637316482034623147/1573396247514105860447863872195300000000000000000)]
    bernstein := [(53523187616202491298039580714214746263393085580710453/1031140964770844416703112067281911808000000000000000000000), (240547164498115985179959869722495497291661443259159991/4124563859083377666812448269127647232000000000000000000000), (1019549090530813157651337683529666148871012549794524077/16498255436333510667249793076510588928000000000000000000000), (4113770546722148857429679732786416111501242758657716319/65993021745334042668999172306042355712000000000000000000000), (15821742800568564700091634664917360774002062441897608293/263972086981336170675996689224169422848000000000000000000000)]
    reserve := (51906761/1000000000000) }

theorem tilt_035_012_valid : tilt_035_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_035_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_035_012]
  · intro i; fin_cases i <;> norm_num [tilt_035_012]
  · norm_num [tilt_035_012]
  · norm_num [tilt_035_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_035_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_035_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_035_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_035_012]

def tilt_035_013 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/160), (29/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14723183/100000000), (14723183/100000000), (9252921/100000000), (7317651/50000000), (7317651/50000000), (16180483/100000000), (3962407/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(4373/80000), (1/100000000), (1054387/25000000), (4375187/100000000), (1/100000000), (1377533/25000000), (379699/100000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-14865317402009454211391650240791672163450943/1055158264465130998811435117900000000000000000), (12676108020894528712931/20017484475650000000000), (-3733737317908924331472456215871276342575450943/527579132232565499405717558950000000000000000), (12676108020894528712931/20017484475650000000000), (-7452609318415839208733520781501761012987450943/1055158264465130998811435117900000000000000000)]
    bernstein := [(67523284501341958206096108863945484288064280007457/691508520199868251381062118866944000000000000000000000), (286597277326592797220509844930617727578668095370779/2766034080799473005524248475467776000000000000000000000), (1180553444907572889105488196138935466645339143037113/11064136323197892022096993901871104000000000000000000000), (4731436794269771605548652302078723482294021986968611/44256545292791568088387975607484416000000000000000000000), (18452792707844244706502277703469083699385357805494417/177026181171166272353551902429937664000000000000000000000)]
    reserve := (6102897/62500000000) }

theorem tilt_035_013_valid : tilt_035_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_035_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_035_013]
  · intro i; fin_cases i <;> norm_num [tilt_035_013]
  · norm_num [tilt_035_013]
  · norm_num [tilt_035_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_035_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_035_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_035_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_035_013]

def tilt_035_014 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/160), (29/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14723183/100000000), (14723183/100000000), (9252921/100000000), (7317651/50000000), (7317651/50000000), (16180483/100000000), (3962407/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(4373/80000), (1/100000000), (1054387/25000000), (4375187/100000000), (1/100000000), (5515617/100000000), (371817/100000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-19851504549300186584850727070398973532244711/1379044336981534068560349023100000000000000000), (12680566275051419511569/19601950558950000000000), (-1659512485901555927112180714016011276154748237/229840722830255678093391503850000000000000000), (12680566275051419511569/19601950558950000000000), (-9937223410860035376088233557025668683396244711/1379044336981534068560349023100000000000000000)]
    bernstein := [(103592483537202563963339474824658566330882844532089/903770496684218167171710335778816000000000000000000000), (437572066993699432079953919564352070743287973981283/3615081986736872668686841343115264000000000000000000000), (1800625936425327252895253982413706643174824228478801/14460327946947490674747365372461056000000000000000000000), (7233937091556098424963964447648581622555621546984747/57841311787789962698989461489844224000000000000000000000), (28381666995705945899296970615789448320013848560540009/231365247151159850795957845959376896000000000000000000000)]
    reserve := (22924511/200000000000) }

theorem tilt_035_014_valid : tilt_035_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_035_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_035_014]
  · intro i; fin_cases i <;> norm_num [tilt_035_014]
  · norm_num [tilt_035_014]
  · norm_num [tilt_035_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_035_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_035_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_035_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_035_014]

def tilt_035_015 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/160), (29/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14723183/100000000), (14723183/100000000), (9252921/100000000), (7317651/50000000), (7317651/50000000), (16180483/100000000), (3962407/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(2927/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(4373/80000), (1/100000000), (1054387/25000000), (4375187/100000000), (1/100000000), (2756437/50000000), (379699/100000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-89592178968645078773437026368822141967847559/6334100049205657421573484879300000000000000000), (12676108020894528712931/20017484475650000000000), (-22413927887357363730594170964705245893971847559/3167050024602828710786742439650000000000000000), (12676108020894528712931/20017484475650000000000), (-44738263595746082382414904903041669645975847559/6334100049205657421573484879300000000000000000)]
    bernstein := [(171211467145111262134352599748010721000788727751641/4151115808247419647802399050498048000000000000000000000), (261285361511563896415205426051822024029700090907009/5534821077663226197069865400664064000000000000000000000), (10020761142005880687273015320497618012449567626124307/199253558795876143094515154423906304000000000000000000000), (4471777894336626802579873733517299181506492479686681/88557137242611619153117846410625024000000000000000000000), (50817959697438898125498568210310251150863584525298121/1062685646911339429837414156927500288000000000000000000000)]
    reserve := (8248937/200000000000) }

theorem tilt_035_015_valid : tilt_035_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_035_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_035_015]
  · intro i; fin_cases i <;> norm_num [tilt_035_015]
  · norm_num [tilt_035_015]
  · norm_num [tilt_035_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_035_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_035_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_035_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_035_015]

def tilt_035_016 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/160), (29/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14723183/100000000), (14723183/100000000), (9252921/100000000), (7317651/50000000), (7317651/50000000), (16180483/100000000), (3962407/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (867/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(4373/80000), (1/100000000), (1054387/25000000), (4375187/100000000), (761/20000000), (2756437/50000000), (371817/100000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-22747523166146112537624270018222408535002623147/1573396247514105860447863872195300000000000000000), (12680566275051419511569/19601950558950000000000), (-1893424188580695421660760248166643287502839541049/262232707919017643407977312032550000000000000000), (12680566275051419511569/19601950558950000000000), (-11337797608318026417426937218981637316482034623147/1573396247514105860447863872195300000000000000000)]
    bernstein := [(53523187616202491298039580714214746263393085580710453/1031140964770844416703112067281911808000000000000000000000), (240547164498115985179959869722495497291661443259159991/4124563859083377666812448269127647232000000000000000000000), (1019549090530813157651337683529666148871012549794524077/16498255436333510667249793076510588928000000000000000000000), (4113770546722148857429679732786416111501242758657716319/65993021745334042668999172306042355712000000000000000000000), (15821742800568564700091634664917360774002062441897608293/263972086981336170675996689224169422848000000000000000000000)]
    reserve := (51906761/1000000000000) }

theorem tilt_035_016_valid : tilt_035_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_035_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_035_016]
  · intro i; fin_cases i <;> norm_num [tilt_035_016]
  · norm_num [tilt_035_016]
  · norm_num [tilt_035_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_035_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_035_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_035_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_035_016]

def tilt_035_017 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/160), (29/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14723183/100000000), (14723183/100000000), (9252921/100000000), (7317651/50000000), (7317651/50000000), (16180483/100000000), (3962407/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(4373/80000), (1/100000000), (1054387/25000000), (4375187/100000000), (1/100000000), (1377533/25000000), (379699/100000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-29730680394922628069057912862025170137946261/2110316528930261997622870235800000000000000000), (12676108020894528712931/20017484475650000000000), (-7467474681408752382591187044122994510961946261/1055158264465130998811435117900000000000000000), (12676108020894528712931/20017484475650000000000), (-14905218682422582137113316175383963851785946261/2110316528930261997622870235800000000000000000)]
    bernstein := [(135016576060099197350217795197158111631566514470539/1383017040399736502762124237733888000000000000000000000), (573074574697319091656670917007682360647495668343433/5532068161598946011048496950935552000000000000000000000), (7081880810574878784713598277378556429285683547274553/66384817939187352132581963411226624000000000000000000000), (9460953642613159988776321537418580511170232213104097/88513090585583136176775951214968832000000000000000000000), (36897905089324049229455861792761514805695853502394459/354052362342332544707103804859875328000000000000000000000)]
    reserve := (19524933/200000000000) }

theorem tilt_035_017_valid : tilt_035_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_035_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_035_017]
  · intro i; fin_cases i <;> norm_num [tilt_035_017]
  · norm_num [tilt_035_017]
  · norm_num [tilt_035_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_035_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_035_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_035_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_035_017]

def tilt_035_018 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/160), (29/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14723183/100000000), (14723183/100000000), (9252921/100000000), (7317651/50000000), (7317651/50000000), (16180483/100000000), (3962407/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(4373/80000), (1/100000000), (1054387/25000000), (4375187/100000000), (1/100000000), (5515617/100000000), (371817/100000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-19830225581225402919551705780071527152033461/1379044336981534068560349023100000000000000000), (12680566275051419511569/19601950558950000000000), (-1659505392912197665890414373585902127361344487/229840722830255678093391503850000000000000000), (12680566275051419511569/19601950558950000000000), (-9937202131891960592422934535735341237016033461/1379044336981534068560349023100000000000000000)]
    bernstein := [(117591303820601151668788635216945399743560515743339/903770496684218167171710335778816000000000000000000000), (493571168617058833785369343313028665099440927285033/3615081986736872668686841343115264000000000000000000000), (2024637807501022070403067624093584083675188881880051/14460327946947490674747365372461056000000000000000000000), (8130047164829647342870019730070140750168151248218497/57841311787789962698989461489844224000000000000000000000), (31966360567867273457109892617800960165636435649651259/231365247151159850795957845959376896000000000000000000000)]
    reserve := (32527977/250000000000) }

theorem tilt_035_018_valid : tilt_035_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_035_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_035_018]
  · intro i; fin_cases i <;> norm_num [tilt_035_018]
  · norm_num [tilt_035_018]
  · norm_num [tilt_035_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_035_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_035_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_035_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_035_018]

def tilt_035_019 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/160), (29/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14723183/100000000), (14723183/100000000), (9252921/100000000), (7317651/50000000), (7317651/50000000), (16180483/100000000), (3962407/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(4373/80000), (1/100000000), (1054387/25000000), (4375187/100000000), (1/100000000), (2756437/50000000), (375757/100000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-29575123578963562751549236114937430463531161/2089446668887171343404633633300000000000000000), (269925582911831/421754800000000), (-7467796691916492270150845488088966741504309161/1044723334443585671702316816650000000000000000), (269925582911831/421754800000000), (-14906018260254020977550141740062996052545087161/2089446668887171343404633633300000000000000000)]
    bernstein := [(261908251676523498526511624547038958541926749649639/1369339768921896611613660697919488000000000000000000000), (1081506661063864370931808658300212341495741832051133/5477359075687586446454642791677952000000000000000000000), (13193443599019035063894276922602733188205265543710253/65728308908251037357455713500135424000000000000000000000), (17623531920512635855400264369566347881291688398353397/87637745211001383143274284666847232000000000000000000000), (69603493456734054723522431480444750051279125524621559/350550980844005532573097138667388928000000000000000000000)]
    reserve := (191266081/1000000000000) }

theorem tilt_035_019_valid : tilt_035_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_035_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_035_019]
  · intro i; fin_cases i <;> norm_num [tilt_035_019]
  · norm_num [tilt_035_019]
  · norm_num [tilt_035_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_035_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_035_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_035_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_035_019]

def tilt_035_020 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/160), (29/640)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(14723183/100000000), (14723183/100000000), (9252921/100000000), (7317651/50000000), (7317651/50000000), (16180483/100000000), (3962407/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(4373/80000), (1/100000000), (1054387/25000000), (4375187/100000000), (1/100000000), (2756437/50000000), (375757/100000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-29899380064464224498453251679970909872531161/2089446668887171343404633633300000000000000000), (269925582911831/421754800000000), (-7467458609353438915102445029722718352665309161/1044723334443585671702316816650000000000000000), (269925582911831/421754800000000), (-14905017838642413605706436807765465795458087161/2089446668887171343404633633300000000000000000)]
    bernstein := [(50254104885287542520719789338388221126235836649639/1369339768921896611613660697919488000000000000000000000), (234951001438832489461857070396619155991107821051133/5477359075687586446454642791677952000000000000000000000), (1011838538657728956355448993096985275916427764236751/21909436302750345785818571166711808000000000000000000000), (4080626262694623483527146268272590231797773099353397/87637745211001383143274284666847232000000000000000000000), (15435911104661663700828775199521168780728736771621559/350550980844005532573097138667388928000000000000000000000)]
    reserve := (18349757/500000000000) }

theorem tilt_035_020_valid : tilt_035_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_035_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_035_020]
  · intro i; fin_cases i <;> norm_num [tilt_035_020]
  · norm_num [tilt_035_020]
  · norm_num [tilt_035_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_035_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_035_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_035_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_035_020]

def tiltBundle035_row : Alternative → Row
  | .zero => tilt_035_000
  | (.spike 0 false false) => tilt_035_001
  | (.spike 0 false true) => tilt_035_002
  | (.spike 0 true false) => tilt_035_003
  | (.spike 0 true true) => tilt_035_004
  | (.spike 1 false false) => tilt_035_005
  | (.spike 1 false true) => tilt_035_006
  | (.spike 1 true false) => tilt_035_007
  | (.spike 1 true true) => tilt_035_008
  | (.spike 2 false false) => tilt_035_009
  | (.spike 2 false true) => tilt_035_010
  | (.spike 2 true false) => tilt_035_011
  | (.spike 2 true true) => tilt_035_012
  | (.spike 3 false false) => tilt_035_013
  | (.spike 3 false true) => tilt_035_014
  | (.spike 3 true false) => tilt_035_015
  | (.spike 3 true true) => tilt_035_016
  | (.spike 4 false false) => tilt_035_017
  | (.spike 4 false true) => tilt_035_018
  | (.spike 4 true false) => tilt_035_019
  | (.spike 4 true true) => tilt_035_020

def tiltBundle035 : TiltBundle where
  interval := ⟨(7/160), (29/640)⟩
  lambda := ![(14723183/100000000), (14723183/100000000), (9252921/100000000), (7317651/50000000), (7317651/50000000), (16180483/100000000), (3962407/25000000)]
  row := tiltBundle035_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_035_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_035_001_valid | exact tilt_035_002_valid | exact tilt_035_003_valid | exact tilt_035_004_valid | exact tilt_035_005_valid | exact tilt_035_006_valid | exact tilt_035_007_valid | exact tilt_035_008_valid | exact tilt_035_009_valid | exact tilt_035_010_valid | exact tilt_035_011_valid | exact tilt_035_012_valid | exact tilt_035_013_valid | exact tilt_035_014_valid | exact tilt_035_015_valid | exact tilt_035_016_valid | exact tilt_035_017_valid | exact tilt_035_018_valid | exact tilt_035_019_valid | exact tilt_035_020_valid
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
