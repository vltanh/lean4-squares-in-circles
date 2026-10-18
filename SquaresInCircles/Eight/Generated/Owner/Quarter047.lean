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

def quarter_047_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 3, 0, 2, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(102465129/100000000), 0, (19192791/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(560543/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-9336687063886503438164777/457463486508250000000000), (-64079547/560543), (-40663458022347003438164777/228731743254125000000000), (-64079547/560543), (-71990228980807503438164777/457463486508250000000000)]
    bernstein := [(703685342559292178019903367/1873770440737792000000000000), (1875854259774222321528801499/4684426101844480000000000000), (14277826683957307031840585677/35133195763833600000000000000), (11531305198752544833786737987/29277663136528000000000000000), (26588901590914354362542792023/73194157841320000000000000000)]
    reserve := (36326535307/100000000000) }

theorem quarter_047_000_valid : quarter_047_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_047_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_047_000]
  · intro i; fin_cases i <;> norm_num [quarter_047_000]
  · norm_num [quarter_047_000]
  · norm_num [quarter_047_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_047_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_047_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_047_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_047_000]

def quarter_047_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(100371721/100000000), 0, (19887081/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(71153/12500000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-8208487042318949692827207/464548117886000000000000), (-60597559/569224), (-40668488900274449692827207/232274058943000000000000), (-60597559/569224), (-73128490758229949692827207/464548117886000000000000)]
    bernstein := [(25542887225243746976342241593/74327698861760000000000000000), (54783549554092372087240394787/148655397723520000000000000000), (111418677708706730449600452033/297310795447040000000000000000), (215717198152734591859305697947/594621590894080000000000000000), (396003581849212929304558675273/1189243181788160000000000000000)]
    reserve := (83246973351/250000000000) }

theorem quarter_047_001_valid : quarter_047_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_047_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_047_001]
  · intro i; fin_cases i <;> norm_num [quarter_047_001]
  · norm_num [quarter_047_001]
  · norm_num [quarter_047_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_047_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_047_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_047_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_047_001]

def quarter_047_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 3, 0, 2, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(19608541/20000000), 0, (41103203/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(577517/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-1426099006298046362438957/94263219891350000000000), (-56939502/577517), (-8135027509922696362438957/47131609945675000000000), (-56939502/577517), (-14843956013547346362438957/94263219891350000000000)]
    bernstein := [(74943659209813187891663083523/241313842921856000000000000000), (20236252696962981297167944413/60328460730464000000000000000), (15471642832850517916961408309/45246345547848000000000000000), (1246171032223673960933468593/3770528795654000000000000000), (284174818686034867862751883/942632198913500000000000000)]
    reserve := (301469458621/1000000000000) }

theorem quarter_047_002_valid : quarter_047_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_047_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_047_002]
  · intro i; fin_cases i <;> norm_num [quarter_047_002]
  · norm_num [quarter_047_002]
  · norm_num [quarter_047_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_047_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_047_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_047_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_047_002]

def quarter_047_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(47737769/50000000), 0, (84730841/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(585377/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-9773973405635598256572169/764369130194800000000000), (-106220235/1170754), (-65093570208929798256572169/382184565097400000000000), (-106220235/1170754), (-120413167012223998256572169/764369130194800000000000)]
    bernstein := [(2111975726260626713666060111/7643691301948000000000000000), (9208591601509896784563339707/30574765207792000000000000000), (37663862899051992598321534059/122299060831168000000000000000), (145308269583885004690215666383/489196243324672000000000000000), (525814725929969699756030396871/1956784973298688000000000000000)]
    reserve := (16794599723/62500000000) }

theorem quarter_047_003_valid : quarter_047_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_047_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_047_003]
  · intro i; fin_cases i <;> norm_num [quarter_047_003]
  · norm_num [quarter_047_003]
  · norm_num [quarter_047_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_047_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_047_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_047_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_047_003]

def quarter_047_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 3, 0, 2, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(231673/250000), 0, (21776787/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(592757/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-8238678976211038309129793/774005730506800000000000), (-49115626/592757), (-65109733826768638309129793/387002865253400000000000), (-49115626/592757), (-121980788677326238309129793/774005730506800000000000)]
    bernstein := [(477272706590133896248704771087/1981454670097408000000000000000), (52661339155095844167884088237/198145467009740800000000000000), (16217359561567344995261091973/59443640102922240000000000000), (519868938481048435359691749/1981454670097408000000000000), (46506272043574728661489823/198145467009740800000000000)]
    reserve := (9388309053/40000000000) }

theorem quarter_047_004_valid : quarter_047_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_047_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_047_004]
  · intro i; fin_cases i <;> norm_num [quarter_047_004]
  · norm_num [quarter_047_004]
  · norm_num [quarter_047_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_047_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_047_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_047_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_047_004]

def quarter_047_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(22406079/25000000), 0, (44660553/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(299807/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-17030661182269892909521343/1957398529634000000000000), (-44963763/599614), (-162821954872612892909521343/978699264817000000000000), (-44963763/599614), (-308613248562955892909521343/1957398529634000000000000)]
    bernstein := [(102349856194342949148331873/501094023586304000000000000), (1148422154004984670945181561/5010940235863040000000000000), (826745766726247431323963401/3496004815718400000000000000), (113485721831883046226991188473/501094023586304000000000000000), (999296720257540176098060282977/5010940235863040000000000000000)]
    reserve := (99711498563/500000000000) }

theorem quarter_047_005_valid : quarter_047_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_047_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_047_005]
  · intro i; fin_cases i <;> norm_num [quarter_047_005]
  · norm_num [quarter_047_005]
  · norm_num [quarter_047_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_047_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_047_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_047_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_047_005]

def quarter_047_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 3, 0, 2, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(345373/400000), 0, (22839737/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(37869/6250000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-1719924153567237495332851/247241475078000000000000), (-847162/12623), (-20359610527228987495332851/123620737539000000000000), (-847162/12623), (-12999765633630245831777617/82413825026000000000000)]
    bernstein := [(8102730097404880342365201953/48687552015360000000000000000), (15141896346211681502204791021/79117272024960000000000000000), (113495363872629455994497791/570557250180000000000000000), (39006384597562700060214611/206034562565000000000000000), (483828052294162560672937/2971652344687500000000000)]
    reserve := (40703621771/250000000000) }

theorem quarter_047_006_valid : quarter_047_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_047_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_047_006]
  · intro i; fin_cases i <;> norm_num [quarter_047_006]
  · norm_num [quarter_047_006]
  · norm_num [quarter_047_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_047_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_047_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_047_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_047_006]

def quarter_047_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(82830189/100000000), 0, (93207547/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(611587/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-2160864767049455192679741/399296712399400000000000), (-72452831/1223174), (-32587825353125155192679741/199648356199700000000000), (-72452831/1223174), (-63014785939200855192679741/399296712399400000000000)]
    bernstein := [(7944486300681222437123771/62390111312406250000000000), (152061772474782676498816969/998241780998500000000000000), (1917553159418961854195085037/11978901371982000000000000000), (19273738542380305840119167837/127774947967808000000000000000), (127591957454070811210055593059/1022199583742464000000000000000)]
    reserve := (15602622947/125000000000) }

theorem quarter_047_007_valid : quarter_047_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_047_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_047_007]
  · intro i; fin_cases i <;> norm_num [quarter_047_007]
  · norm_num [quarter_047_007]
  · norm_num [quarter_047_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_047_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_047_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_047_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_047_007]

def quarter_047_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 3, 0, 2, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(39545593/50000000), 0, (4742731/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(616623/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-16370826726713111514700481/4025846473026000000000000), (-31663876/616623), (-108672396249311037171566827/670974412171000000000000), (-31663876/616623), (-635663550769153111514700481/4025846473026000000000000)]
    bernstein := [(895909533610578656114937364319/10306166970946560000000000000000), (576888836997731191164562508251/5153083485473280000000000000000), (308891134286058906651146355479/2576541742736640000000000000000), (142956559643048917590240185491/1288270871368320000000000000000), (54986761533290832709388837839/644135435684160000000000000000)]
    reserve := (10670652181/125000000000) }

theorem quarter_047_008_valid : quarter_047_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_047_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_047_008]
  · intro i; fin_cases i <;> norm_num [quarter_047_008]
  · norm_num [quarter_047_008]
  · norm_num [quarter_047_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_047_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_047_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_047_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_047_008]

def quarter_047_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 3, 0, 2, 0, 0, 3]
    lambda := ![(1/100000000), (1/100000000), (1/100000000), (1/25000000), (3/100000000), (3/100000000), (24999997/25000000)]
    cone := fun i => (![![(75134173/100000000), 0, (962889/1000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5223089/20000000), 0, 0]] i.1) i.2
    mu := ![(31049/5000000), (1/100000000), (1/100000000), (1/50000000), (1/100000000), (1/100000000), (5223089/20000000)]
    alternative := .zero
    polynomial := [(-947333756048117220494317/324343380722000000000000), (-674742994341321/15524500000000), (-26093605721876286312970317/162171690361000000000000), (-674742994341321/15524500000000), (-51239877687704455405446317/324343380722000000000000)]
    bernstein := [(2341872309918481069134885923/51894940915520000000000000000), (1456503085367668341304388561/20757976366208000000000000000), (649807010571805740977524603/8303190546483200000000000000), (46238527555024477229519077/664255243718656000000000000), (2356974608286878374926027/53140419497492480000000000)]
    reserve := (22176853613/500000000000) }

theorem quarter_047_009_valid : quarter_047_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_047_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_047_009]
  · intro i; fin_cases i <;> norm_num [quarter_047_009]
  · norm_num [quarter_047_009]
  · norm_num [quarter_047_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_047_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_047_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_047_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_047_009]

def quarter_047_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 3, 0, 2, 0, 0, 3]
    lambda := ![(6714353/100000000), (10529247/100000000), (5771227/50000000), (10721243/50000000), (10721243/50000000), (10721243/50000000), (6886489/100000000)]
    cone := fun i => (![![(306019/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3699119/50000000), 0, 0]] i.1) i.2
    mu := ![(8603/20000000), (1577721/50000000), (184231/25000000), (1538301/25000000), (1/100000000), (1/100000000), (7398239/100000000)]
    alternative := .zero
    polynomial := [(-960481665988048423073444674059542179043/18972355724513351327277726378000000000000), (-326937528739/122900000000), (-118575287854595732238243457551637242076043/9486177862256675663638863189000000000000), (-326937528739/122900000000), (-236190094043203416053413470429214941973043/18972355724513351327277726378000000000000)]
    bernstein := [(275859653252906657245122510677186141461333/3108430761904267481461182689771520000000000), (592407866433988067231250888738589470203107/6475897420633890586377463937024000000000000), (33837847638006753708593670947853628521910459/364269229910656345483732346457600000000000000), (46585657920799554377718440167742092817839/500920283155468021842316208000000000000000), (172462723485706547688962604259375459922657/1878451061833005081908685780000000000000000)]
    reserve := (22186408061/250000000000) }

theorem quarter_047_010_valid : quarter_047_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_047_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_047_010]
  · intro i; fin_cases i <;> norm_num [quarter_047_010]
  · norm_num [quarter_047_010]
  · norm_num [quarter_047_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_047_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_047_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_047_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_047_010]

def quarter_047_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 3]
    lambda := ![(1625301/25000000), (2172883/20000000), (11711149/100000000), (2144057/10000000), (2144057/10000000), (2144057/10000000), (3300761/50000000)]
    cone := fun i => (![![(1146489/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3661659/50000000), 0, 0]] i.1) i.2
    mu := ![(41427/100000000), (199949/6250000), (30311/5000000), (6173097/100000000), (1/100000000), (1/100000000), (3661659/50000000)]
    alternative := .zero
    polynomial := [(2528527378196275773938382802844511527/280258605189693726945091596000000000000), (-705727716389/345225000000), (-1743299546887297591556190253822698623473/140129302594846863472545798000000000000), (-705727716389/345225000000), (-3489127621152791458886318890448241758473/280258605189693726945091596000000000000)]
    bernstein := [(251785315190991224436869826480895835216927/2802586051896937269450915960000000000000000), (1037433474073879626638806759317424750173481/11210344207587749077803663840000000000000000), (12636504709247517015648158467037630395728329/134524130491052988933643966080000000000000000), (16865529081589408325545326985155906758628029/179365507321403985244858621440000000000000000), (66602754155908266880221129304551289461861287/717462029285615940979434485760000000000000000)]
    reserve := (89840351207/1000000000000) }

theorem quarter_047_011_valid : quarter_047_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_047_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_047_011]
  · intro i; fin_cases i <;> norm_num [quarter_047_011]
  · norm_num [quarter_047_011]
  · norm_num [quarter_047_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_047_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_047_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_047_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_047_011]

def quarter_047_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 3, 0, 2, 0, 0, 3]
    lambda := ![(784999/12500000), (2805513/25000000), (11871601/100000000), (21432369/100000000), (21432369/100000000), (21432369/100000000), (6329247/100000000)]
    cone := fun i => (![![(788077/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (725007/10000000), 0, 0]] i.1) i.2
    mu := ![(7971/20000000), (1624699/50000000), (466103/100000000), (3095411/50000000), (1/100000000), (1/100000000), (7250071/100000000)]
    alternative := .zero
    polynomial := [(13140202016306264996580802820431919483/253918169141475176725964082000000000000), (-1960814584313/1328500000000), (-1615910394778859448969418757807176728517/126959084570737588362982041000000000000), (-1960814584313/1328500000000), (-3244960991574025162935418318434785376517/253918169141475176725964082000000000000)]
    bernstein := [(5381736562624386048752518204613654662706593/59093683000197859310769822720000000000000000), (30472761483600243913339436118625553460650041/325015256501088226209234024960000000000000000), (46367554967117222901186361132870266164342441/487522884751632339313851037440000000000000000), (7729842538100678911147919303406140574576449/81253814125272056552308506240000000000000000), (3812141637576629543282336370373135042609883/40626907062636028276154253120000000000000000)]
    reserve := (91071266663/1000000000000) }

theorem quarter_047_012_valid : quarter_047_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_047_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_047_012]
  · intro i; fin_cases i <;> norm_num [quarter_047_012]
  · norm_num [quarter_047_012]
  · norm_num [quarter_047_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_047_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_047_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_047_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_047_012]

def quarter_047_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 3]
    lambda := ![(756059/12500000), (1160499/10000000), (12023421/100000000), (21419203/100000000), (21419203/100000000), (21419203/100000000), (1516377/25000000)]
    cone := fun i => (![![(227137/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1435551/20000000), 0, 0]] i.1) i.2
    mu := ![(38277/100000000), (3306729/100000000), (316297/100000000), (6206599/100000000), (1/100000000), (1/100000000), (1794439/25000000)]
    alternative := .zero
    polynomial := [(2359828337721326637695003352252798400421/29725057040605617236997253937400000000000), (-303650915471/318975000000), (-205656637020841907449925930202643859545579/14862528520302808618498626968700000000000), (-303650915471/318975000000), (-413673102379405141537546863757540517491579/29725057040605617236997253937400000000000)]
    bernstein := [(439575622256454540109499514738825122937885221/4756009126496898757919560629984000000000000000), (301603028175111498137722964609252210479711207/3170672750997932505279707086656000000000000000), (785735254800126475448090106875112361098999209/8153158502566112156433532508544000000000000000), (1219820572990046324505523855490342967876279607/12682691003991730021118828346624000000000000000), (7194786558559080937367401366565191706015375621/76096146023950380126712970079744000000000000000)]
    reserve := (2310632773/25000000000) }

theorem quarter_047_013_valid : quarter_047_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_047_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_047_013]
  · intro i; fin_cases i <;> norm_num [quarter_047_013]
  · norm_num [quarter_047_013]
  · norm_num [quarter_047_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_047_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_047_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_047_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_047_013]

def quarter_047_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 3, 0, 2, 0, 0, 3]
    lambda := ![(725511/12500000), (6008319/50000000), (3041591/25000000), (668823/3125000), (668823/3125000), (668823/3125000), (2902951/50000000)]
    cone := fun i => (![![(1161/800000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (7105553/100000000), 0, 0]] i.1) i.2
    mu := ![(18337/50000000), (842999/25000000), (15733/10000000), (6220653/100000000), (1/100000000), (1/100000000), (3552777/50000000)]
    alternative := .zero
    polynomial := [(335043844776934808705647233158869638511/3583270159651759598043930666000000000000), (-861988945887/1833700000000), (-32776181389358245665698760457865656913489/1791635079825879799021965333000000000000), (-861988945887/1833700000000), (-65887406623493426140103168148890183465489/3583270159651759598043930666000000000000)]
    bernstein := [(860633471164281938050386584205340811147929711/9173171608708504570992462504960000000000000000), (276918698780361740890958896849640908394743/2866616127721407678435144532800000000000000), (1676500072779059417620757556411098547539311/17199696766328446070610867196800000000000000), (172785766098838788805914741459975961943/1791635079825879799021965333000000000000), (335043844776934808705647233158869638511/3583270159651759598043930666000000000000)]
    reserve := (23375564069/250000000000) }

theorem quarter_047_014_valid : quarter_047_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_047_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_047_014]
  · intro i; fin_cases i <;> norm_num [quarter_047_014]
  · norm_num [quarter_047_014]
  · norm_num [quarter_047_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_047_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_047_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_047_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_047_014]

def quarter_047_015 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 3]
    lambda := ![(5568427/100000000), (12371803/100000000), (6183969/50000000), (425523/2000000), (425523/2000000), (425523/2000000), (2931691/50000000)]
    cone := fun i => (![![0, 0, (293123/100000000), 0, 0], ![0, 0, 0, 0, 0], ![(309247/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (708761/10000000), 0, 0]] i.1) i.2
    mu := ![(37037/100000000), (10713/312500), (78147/100000000), (1243679/20000000), (1/100000000), (1/100000000), (7087611/100000000)]
    alternative := .zero
    polynomial := [(970822704369496075585082814586362451/10562994000267875642227752000000000000), (4335676716443089/5168447212500000), (-13768348512860591314205340939162977959/480136090921267074646716000000000000), (4335676716443089/5168447212500000), (-303874489987302504988102583476171877549/10562994000267875642227752000000000000)]
    bernstein := [(970822704369496075585082814586362451/10562994000267875642227752000000000000), (1026204095118886302419791808271694451/10562994000267875642227752000000000000), (5040158498526260835965345099062934207251/50702371201285803082693209600000000000000), (185305616704172188390367959076740677339/1877865600047622336396044800000000000000), (285312918135309095219106459399606742591739/3004584960076195738233671680000000000000000)]
    reserve := (91907910233/1000000000000) }

theorem quarter_047_015_valid : quarter_047_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_047_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_047_015]
  · intro i; fin_cases i <;> norm_num [quarter_047_015]
  · norm_num [quarter_047_015]
  · norm_num [quarter_047_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_047_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_047_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_047_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_047_015]

def quarter_047_016 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 3, 0, 2, 0, 0, 3]
    lambda := ![(2694949/50000000), (1279889/10000000), (199421/1562500), (426017/2000000), (426017/2000000), (426017/2000000), (5145717/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(958569/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6906639/100000000), 0, 0]] i.1) i.2
    mu := ![(146529/100000000), (3509093/100000000), (80769/100000000), (6274503/100000000), (1/100000000), (1/100000000), (86333/1250000)]
    alternative := .zero
    polynomial := [(1307868116015631556460153838233/17729258844794165487000000000000), (4419651829/2725000000), (-1752786044003549980298163354965903/79781664801573744691500000000000), (4419651829/2725000000), (-3517342901051240644604468094475903/159563329603147489383000000000000)]
    bernstein := [(41094033190704707422603845257419754497/408482123784057572820480000000000000000), (1116698162709852553653699019298090363/10749529573264672968960000000000000000), (20044541403975352947033007606040497/191117649930157941120000000000000000), (5289389090472689704009038813960480497/51060265473007196602560000000000000000), (2553113883052373364228234607166721697/25530132736503598301280000000000000000)]
    reserve := (100003940809/1000000000000) }

theorem quarter_047_016_valid : quarter_047_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_047_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_047_016]
  · intro i; fin_cases i <;> norm_num [quarter_047_016]
  · norm_num [quarter_047_016]
  · norm_num [quarter_047_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_047_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_047_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_047_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_047_016]

def quarter_047_017 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 3]
    lambda := ![(1039209/20000000), (6600817/50000000), (13098897/100000000), (10615491/50000000), (10615491/50000000), (10615491/50000000), (4810479/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1643783/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1700211/25000000), 0, 0]] i.1) i.2
    mu := ![(212599/100000000), (358487/10000000), (83129/100000000), (6303521/100000000), (1/100000000), (1/100000000), (1360169/20000000)]
    alternative := .zero
    polynomial := [(2705612501237639221909398227844567806109/108640875556163912368386459746000000000000), (5625100539751/2078225000000), (-41073985860607010705253228057805503010479/1873118544071791592558387237000000000000), (5625100539751/2078225000000), (-2384996792416444260126596625580563742413891/108640875556163912368386459746000000000000)]
    bernstein := [(1835930734326405374726578453319792604971113309/17382540088986225978941833559360000000000000000), (3785542352936837721232017876043352323622656327/34765080177972451957883667118720000000000000000), (7640182631992730025960474567837202714172839381/69530160355944903915767334237440000000000000000), (520728231644897798298645238004544075347119067/4795183472823786476949471326720000000000000000), (29204645121754673221773495772606372453028254029/278120641423779615663069336949760000000000000000)]
    reserve := (52503555601/500000000000) }

theorem quarter_047_017_valid : quarter_047_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_047_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_047_017]
  · intro i; fin_cases i <;> norm_num [quarter_047_017]
  · norm_num [quarter_047_017]
  · norm_num [quarter_047_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_047_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_047_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_047_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_047_017]

def quarter_047_018 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 3, 0, 2, 0, 0, 3]
    lambda := ![(2499629/50000000), (6814199/50000000), (13421299/100000000), (21154293/100000000), (21154293/100000000), (21154293/100000000), (2244083/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(18491/781250), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6696643/100000000), 0, 0]] i.1) i.2
    mu := ![(270949/100000000), (917001/25000000), (85523/100000000), (98911/1562500), (1/100000000), (1/100000000), (6696643/100000000)]
    alternative := .zero
    polynomial := [(-48888118681292133344842938156084517993/900786776944476518222478577344000000000), (1651201469557/427615000000), (-10054571405178870090722790209390418971113/450393388472238259111239288672000000000), (1651201469557/427615000000), (-20060254691676448048100737480624753424233/900786776944476518222478577344000000000)]
    bernstein := [(255243291975459938585412070023814199638438727/2306014148977859886649545158000640000000000000), (9393997754439061711907267244378152334793787/82357648177780710237483755642880000000000000), (7111240202885952124209037077533600863232687/61768236133335532678112816732160000000000000), (586118271718744057868816114255872111721743/5147353011111294389842734727680000000000000), (993244272424060049133780984328337765415167/9007867769444765182224785773440000000000000)]
    reserve := (110264082227/1000000000000) }

theorem quarter_047_018_valid : quarter_047_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_047_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_047_018]
  · intro i; fin_cases i <;> norm_num [quarter_047_018]
  · norm_num [quarter_047_018]
  · norm_num [quarter_047_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_047_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_047_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_047_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_047_018]

def quarter_047_019 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 3, 0, 2, 0, 0, 3]
    lambda := ![(599873/12500000), (2816343/20000000), (6864863/50000000), (1316921/6250000), (1316921/6250000), (1316921/6250000), (522171/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(3128787/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1318731/20000000), 0, 0]] i.1) i.2
    mu := ![(321617/100000000), (3759119/100000000), (43979/50000000), (1270939/20000000), (1/100000000), (1/100000000), (824207/12500000)]
    alternative := .zero
    polynomial := [(-54956093883343795486265075967685551823/329567760982571319326005489000000000000), (44793552698793/8795800000000), (-49136611276860697531296947859559747108699/2142190446386713575619035678500000000000), (44793552698793/8795800000000), (-97558793333237925721272449731539582043699/4284380892773427151238071357000000000000)]
    bernstein := [(49184966105202368734108694483928876536401/424196127997369024875056570000000000000000), (40550125611420238467045016272052155412881/339356902397895219900045256000000000000000), (9925589969877464156408576913539781048502787/82260113141249801303770970054400000000000000), (524020097516778248925425131279299105456453/4387206034199989402867785069568000000000000), (6253416349049963860835120288422755919913/53996381959384484958372739317760000000000)]
    reserve := (115811765939/1000000000000) }

theorem quarter_047_019_valid : quarter_047_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_047_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_047_019]
  · intro i; fin_cases i <;> norm_num [quarter_047_019]
  · norm_num [quarter_047_019]
  · norm_num [quarter_047_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_047_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_047_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_047_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_047_019]

def quarter_047_020 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 3, 0, 2, 0, 0, 3]
    lambda := ![(459459/10000000), (7282109/50000000), (14023727/100000000), (1049011/5000000), (1049011/5000000), (1049011/5000000), (969201/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1965421/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6491523/100000000), 0, 0]] i.1) i.2
    mu := ![(22793/6250000), (3858869/100000000), (90441/100000000), (6376527/100000000), (1/100000000), (1/100000000), (6491523/100000000)]
    alternative := .zero
    polynomial := [(-154107928117108465718132244678546188801/487813608866939084393503989240000000000), (14487720968171/2261025000000), (-5781431849094129210589200089368531930501/243906804433469542196751994620000000000), (14487720968171/2261025000000), (-97510733077531196200515110547508698053/4169347084332812687123965720000000000)]
    bernstein := [(248934218771208903089987283924231273689/2049317478891264091975171630694400000000), (125097900295404625703567549475382769092801/999042270959491244837896169963520000000000), (677118783928614296115446818121863594894811/5352012165854417383060158053376000000000000), (1304454379355680402039607292752855902690111/10406690322494700467061418437120000000000000), (730555806481799088773111736146217091252963/6003859801439250269458510636800000000000000)]
    reserve := (121471768691/1000000000000) }

theorem quarter_047_020_valid : quarter_047_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_047_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_047_020]
  · intro i; fin_cases i <;> norm_num [quarter_047_020]
  · norm_num [quarter_047_020]
  · norm_num [quarter_047_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_047_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_047_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_047_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_047_020]

def quarter_047_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 3]
    lambda := ![0, (4109491/25000000), (1949021/12500000), (22656623/100000000), (22656623/100000000), (22656623/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2434529/50000000), 0, 0], ![(5204897/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2958439/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2136491/50000000), (101361/100000000), (1389913/20000000), (1/100000000), (1/100000000), (5916879/100000000)]
    alternative := .zero
    polynomial := [(-3657968688948823748785563242909/6526144425802508652600000000000), (21389477377427/2534025000000), (-86168679587111664267459326858909/3263072212901254326300000000000), (21389477377427/2534025000000), (-168679390485274504786133090474909/6526144425802508652600000000000)]
    bernstein := [(132472620986684475968581992191067571/1044183108128401384416000000000000000), (274598371391834458361504136588901799/2088366216256802768832000000000000000), (1671444983377037335437735342737144593/12530197297540816612992000000000000000), (11415050234723164610509629701095087/86118194484816609024000000000000000), (22205529737011781771336332668556003/172236388969633218048000000000000000)]
    reserve := (63433616171/500000000000) }

theorem quarter_047_021_valid : quarter_047_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_047_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_047_021]
  · intro i; fin_cases i <;> norm_num [quarter_047_021]
  · norm_num [quarter_047_021]
  · norm_num [quarter_047_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_047_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_047_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_047_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_047_021]

def quarter_047_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 3, 0, 2, 0, 0, 3]
    lambda := ![0, (8536209/50000000), (7956391/50000000), (22338267/100000000), (22338267/100000000), (22338267/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (1264247/25000000), 0, 0], ![(247389/4000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2916869/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2218953/50000000), (104413/100000000), (6930137/100000000), (1/100000000), (1/100000000), (5833739/100000000)]
    alternative := .zero
    polynomial := [(-15300194909293133807084503215892377977/18733610587899621679816254000000000000), (2111764208301/208826000000), (-259012842209925644874695767878864417977/9366805293949810839908127000000000000), (2111764208301/208826000000), (-502725489510558155942307032541836457977/18733610587899621679816254000000000000)]
    bernstein := [(6481626941659098252286207798863082184483623/47958043105023031500329610240000000000000000), (279910262042928834914241124351904788668963/1998251796042626312513733760000000000000000), (79896259638322647692007178936522918620289/562008317636988650394487620000000000000000), (2207000621759474261540910906731082194631/15611342156583018066513545000000000000000), (402953747212633267140627162982119101887/2927126654359315887471289687500000000000)]
    reserve := (5406081251/40000000000) }

theorem quarter_047_022_valid : quarter_047_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_047_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_047_022]
  · intro i; fin_cases i <;> norm_num [quarter_047_022]
  · norm_num [quarter_047_022]
  · norm_num [quarter_047_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_047_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_047_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_047_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_047_022]

def quarter_047_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 3]
    lambda := ![0, (8869011/50000000), (1620527/10000000), (22018903/100000000), (22018903/100000000), (22018903/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2627073/50000000), 0, 0], ![(144259/2000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1150067/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (4610927/100000000), (26869/25000000), (172703/2500000), (1/100000000), (1/100000000), (89849/1562500)]
    alternative := .zero
    polynomial := [(-1020150364793100951868817392002433/904677824612367279464000000000000), (1279434657849/107476000000), (-13118159699148202543114033517802433/452338912306183639732000000000000), (1279434657849/107476000000), (-25216169033503304134359249643602433/904677824612367279464000000000000)]
    bernstein := [(20333263324261331209768297661188823/141355910095682387416250000000000000), (337215561220260345448841851539689539/2261694561530918198660000000000000000), (4108479332074860014853100653509077889/27140334738371018383920000000000000000), (43611332267496978209982825291003316543/289496903875957529428480000000000000000), (340090750822030196228140950491465323487/2315975231007660235427840000000000000000)]
    reserve := (143844451289/1000000000000) }

theorem quarter_047_023_valid : quarter_047_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_047_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_047_023]
  · intro i; fin_cases i <;> norm_num [quarter_047_023]
  · norm_num [quarter_047_023]
  · norm_num [quarter_047_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_047_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_047_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_047_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_047_023]

def quarter_047_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 3, 0, 2, 0, 0, 3]
    lambda := ![0, (288097/1562500), (16469211/100000000), (21697527/100000000), (21697527/100000000), (21697527/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (5461547/100000000), 0, 0], ![(518157/6250000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2833203/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (4792937/100000000), (110559/100000000), (6883003/100000000), (1/100000000), (1/100000000), (5666407/100000000)]
    alternative := .zero
    polynomial := [(-123916360715537785117372946266585526363/82668781783276365034616172000000000000), (199039302972/14395703125), (-1259211932518029109139169169378213046363/41334390891638182517308086000000000000), (199039302972/14395703125), (-2394507504320520433160965392489840566363/82668781783276365034616172000000000000)]
    bernstein := [(32375919063131146934263623540206912966322757/211632081365187494488617400320000000000000000), (3356322275662000644281432265456833606821693/21163208136518749448861740032000000000000000), (1022721967364784667979908238663123991257263/6348962440955624834658522009600000000000000), (33948326995576091238131114899113437799101/211632081365187494488617400320000000000000), (3312349196519198967310331797650289441093/21163208136518749448861740032000000000000)]
    reserve := (1195172613/7812500000) }

theorem quarter_047_024_valid : quarter_047_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_047_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_047_024]
  · intro i; fin_cases i <;> norm_num [quarter_047_024]
  · norm_num [quarter_047_024]
  · norm_num [quarter_047_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_047_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_047_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_047_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_047_024]

def quarter_047_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 3]
    lambda := ![0, (19176407/100000000), (16704021/100000000), (21373191/100000000), (21373191/100000000), (21373191/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (5680207/100000000), 0, 0], ![(2354653/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (697713/12500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (4984829/100000000), (11367/10000000), (171357/2500000), (1/100000000), (1/100000000), (1116341/20000000)]
    alternative := .zero
    polynomial := [(-27993905640917799953622215998427161/14452187489772673810788000000000000), (107253644351/6750000000), (-231625891834590337272526088322581161/7226093744886336905394000000000000), (107253644351/6750000000), (-435257878028262874591429960646735161/14452187489772673810788000000000000)]
    bernstein := [(601590012419428338391556850171682471/3699759997381804495561728000000000000), (693081228128458079680268147744814997/4110844441535338328401920000000000000), (190152893584209116206845782341423709021/1109927999214541348668518400000000000000), (23392370794098981625983322303651011487/137028148051177944280064000000000000000), (685307841259695126265813889643802116511/4110844441535338328401920000000000000000)]
    reserve := (162602442549/1000000000000) }

theorem quarter_047_025_valid : quarter_047_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_047_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_047_025]
  · intro i; fin_cases i <;> norm_num [quarter_047_025]
  · norm_num [quarter_047_025]
  · norm_num [quarter_047_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_047_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_047_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_047_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_047_025]

def quarter_047_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 3, 0, 2, 0, 0, 3]
    lambda := ![0, (9978043/50000000), (105681/625000), (4208997/20000000), (4208997/20000000), (4208997/20000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2955577/50000000), 0, 0], ![(10598701/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (686999/12500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (5187503/100000000), (116819/100000000), (1705361/25000000), (1/100000000), (1/100000000), (686999/12500000)]
    alternative := .zero
    polynomial := [(-1738598349370312136611098353688143743/709976995233981122436523000000000000), (105754294322143/5840950000000), (-11992592387124860023041547766505743743/354988497616990561218261500000000000), (105754294322143/5840950000000), (-22246586424879407909471997179323343743/709976995233981122436523000000000000)]
    bernstein := [(313966703084916390667922783399118533689137/1817541107798991673437498880000000000000000), (81405700949171338722191340681273050972601/454385276949747918359374720000000000000000), (62066068461333315574695105550844199231719/340788957712310938769531040000000000000000), (5156862823350355446452987535647648111629/28399079809359244897460920000000000000000), (1259941240353222833519338386729900389417/7099769952339811224365230000000000000000)]
    reserve := (17274255957/100000000000) }

theorem quarter_047_026_valid : quarter_047_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_047_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_047_026]
  · intro i; fin_cases i <;> norm_num [quarter_047_026]
  · norm_num [quarter_047_026]
  · norm_num [quarter_047_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_047_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_047_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_047_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_047_026]

def quarter_047_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 3, 0, 2, 0, 0, 3]
    lambda := ![0, (20780791/100000000), (17083141/100000000), (20712023/100000000), (20712023/100000000), (20712023/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (3077719/50000000), 0, 0], ![(11832479/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5409037/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2700941/50000000), (120013/100000000), (6783983/100000000), (1/100000000), (1/100000000), (2704519/50000000)]
    alternative := .zero
    polynomial := [(-4523242654036506708559139827735728081/1486819286505370588458060250000000000), (245888273110889/12001300000000), (-26513468931055923707208328489484186831/743409643252685294229030125000000000), (245888273110889/12001300000000), (-48503695208075340705857517151232645581/1486819286505370588458060250000000000)]
    bernstein := [(2727402476764377161471909907177502877139/14868192865053705884580602500000000000000), (11317861502551057127240398142532798847319/59472771460214823538322410000000000000000), (138123229857832983066144574225081978581697/713673257522577882459868920000000000000000), (183719971366456065932057496464484869436879/951564343363437176613158560000000000000000), (718685193318823592692320698962939132096259/3806257373453748706452634240000000000000000)]
    reserve := (183438734049/1000000000000) }

theorem quarter_047_027_valid : quarter_047_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_047_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_047_027]
  · intro i; fin_cases i <;> norm_num [quarter_047_027]
  · norm_num [quarter_047_027]
  · norm_num [quarter_047_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_047_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_047_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_047_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_047_027]

def quarter_047_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 3, 0, 2, 0, 0, 3]
    lambda := ![0, (21654179/100000000), (269149/1562500), (5093357/25000000), (5093357/25000000), (5093357/25000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (6414143/100000000), 0, 0], ![(820119/6250000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1330153/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1407229/25000000), (123261/100000000), (52667/781250), (1/100000000), (1/100000000), (1330153/25000000)]
    alternative := .zero
    polynomial := [(-724413353205115310751639663562269407/194424336293084917347504000000000000), (5919667875767/256793750000), (-3666188060313258857935027888120349407/97212168146542458673752000000000000), (5919667875767/256793750000), (-2202654255807134135039472037559476469/64808112097694972449168000000000000)]
    bernstein := [(96920319096096634255217207248226707681073/497726300910297388409610240000000000000000), (4571810944416875887480780421211376700377/22623922768649881291345920000000000000000), (76749460564675741458165648638022866461499/373294725682723041307207680000000000000000), (1160654030080663687748793581057311296817/5655980692162470322836480000000000000000), (6246685632550544303933531426890775519393/31107893806893586775600640000000000000000)]
    reserve := (97363067733/500000000000) }

theorem quarter_047_028_valid : quarter_047_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_047_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_047_028]
  · intro i; fin_cases i <;> norm_num [quarter_047_028]
  · norm_num [quarter_047_028]
  · norm_num [quarter_047_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_047_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_047_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_047_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_047_028]

def quarter_047_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 3, 0, 2, 0, 0, 3]
    lambda := ![0, (11290031/50000000), (17334977/100000000), (125177/625000), (125177/625000), (125177/625000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (6688397/100000000), 0, 0], ![(7234601/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1046097/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1173919/20000000), (126571/100000000), (209159/3125000), (1/100000000), (1/100000000), (2615243/50000000)]
    alternative := .zero
    polynomial := [(-62386849797067678113611734612619171/13834169016468917226232000000000000), (81678869562631/3164275000000), (-276299894935598766962914202305659171/6917084508234458613116000000000000), (81678869562631/3164275000000), (-490212940074129855812216669998699171/13834169016468917226232000000000000)]
    bernstein := [(457387009835364416708864136835045227229/2213467042635026756197120000000000000000), (189931381870719943044893227994791952001/885386817054010702478848000000000000000), (77328644186549218486349150148576249957/354154726821604280991539200000000000000), (30886910388815995090917484460883533577/141661890728641712396615680000000000000), (12096100169433200142549235911798037741/56664756291456684958646272000000000000)]
    reserve := (103319137133/500000000000) }

theorem quarter_047_029_valid : quarter_047_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_047_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_047_029]
  · intro i; fin_cases i <;> norm_num [quarter_047_029]
  · norm_num [quarter_047_029]
  · norm_num [quarter_047_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_047_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_047_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_047_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_047_029]

def quarterTable047 : OwnerTable where
  mode := .quarter
  owners := ![0, 3, 0, 2, 0, 0, 3]
  rows := [quarter_047_000, quarter_047_001, quarter_047_002, quarter_047_003, quarter_047_004, quarter_047_005, quarter_047_006, quarter_047_007, quarter_047_008, quarter_047_009, quarter_047_010, quarter_047_011, quarter_047_012, quarter_047_013, quarter_047_014, quarter_047_015, quarter_047_016, quarter_047_017, quarter_047_018, quarter_047_019, quarter_047_020, quarter_047_021, quarter_047_022, quarter_047_023, quarter_047_024, quarter_047_025, quarter_047_026, quarter_047_027, quarter_047_028, quarter_047_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_047_000_valid
    · exact quarter_047_001_valid
    · exact quarter_047_002_valid
    · exact quarter_047_003_valid
    · exact quarter_047_004_valid
    · exact quarter_047_005_valid
    · exact quarter_047_006_valid
    · exact quarter_047_007_valid
    · exact quarter_047_008_valid
    · exact quarter_047_009_valid
    · exact quarter_047_010_valid
    · exact quarter_047_011_valid
    · exact quarter_047_012_valid
    · exact quarter_047_013_valid
    · exact quarter_047_014_valid
    · exact quarter_047_015_valid
    · exact quarter_047_016_valid
    · exact quarter_047_017_valid
    · exact quarter_047_018_valid
    · exact quarter_047_019_valid
    · exact quarter_047_020_valid
    · exact quarter_047_021_valid
    · exact quarter_047_022_valid
    · exact quarter_047_023_valid
    · exact quarter_047_024_valid
    · exact quarter_047_025_valid
    · exact quarter_047_026_valid
    · exact quarter_047_027_valid
    · exact quarter_047_028_valid
    · exact quarter_047_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
