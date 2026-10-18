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

def quarter_019_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 1, 0, 0, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(102465129/100000000), 0, (19192791/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(560543/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-9336687063886503438164777/457463486508250000000000), (-64079547/560543), (-40663458022347003438164777/228731743254125000000000), (-64079547/560543), (-71990228980807503438164777/457463486508250000000000)]
    bernstein := [(703685342559292178019903367/1873770440737792000000000000), (1875854259774222321528801499/4684426101844480000000000000), (14277826683957307031840585677/35133195763833600000000000000), (11531305198752544833786737987/29277663136528000000000000000), (26588901590914354362542792023/73194157841320000000000000000)]
    reserve := (36326535307/100000000000) }

theorem quarter_019_000_valid : quarter_019_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_019_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_019_000]
  · intro i; fin_cases i <;> norm_num [quarter_019_000]
  · norm_num [quarter_019_000]
  · norm_num [quarter_019_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_019_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_019_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_019_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_019_000]

def quarter_019_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(100371721/100000000), 0, (19887081/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(71153/12500000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-8208487042318949692827207/464548117886000000000000), (-60597559/569224), (-40668488900274449692827207/232274058943000000000000), (-60597559/569224), (-73128490758229949692827207/464548117886000000000000)]
    bernstein := [(25542887225243746976342241593/74327698861760000000000000000), (54783549554092372087240394787/148655397723520000000000000000), (111418677708706730449600452033/297310795447040000000000000000), (215717198152734591859305697947/594621590894080000000000000000), (396003581849212929304558675273/1189243181788160000000000000000)]
    reserve := (83246973351/250000000000) }

theorem quarter_019_001_valid : quarter_019_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_019_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_019_001]
  · intro i; fin_cases i <;> norm_num [quarter_019_001]
  · norm_num [quarter_019_001]
  · norm_num [quarter_019_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_019_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_019_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_019_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_019_001]

def quarter_019_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 1, 0, 0, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(19608541/20000000), 0, (41103203/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(577517/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-1426099006298046362438957/94263219891350000000000), (-56939502/577517), (-8135027509922696362438957/47131609945675000000000), (-56939502/577517), (-14843956013547346362438957/94263219891350000000000)]
    bernstein := [(74943659209813187891663083523/241313842921856000000000000000), (20236252696962981297167944413/60328460730464000000000000000), (15471642832850517916961408309/45246345547848000000000000000), (1246171032223673960933468593/3770528795654000000000000000), (284174818686034867862751883/942632198913500000000000000)]
    reserve := (301469458621/1000000000000) }

theorem quarter_019_002_valid : quarter_019_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_019_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_019_002]
  · intro i; fin_cases i <;> norm_num [quarter_019_002]
  · norm_num [quarter_019_002]
  · norm_num [quarter_019_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_019_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_019_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_019_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_019_002]

def quarter_019_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(47737769/50000000), 0, (84730841/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(585377/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-9773973405635598256572169/764369130194800000000000), (-106220235/1170754), (-65093570208929798256572169/382184565097400000000000), (-106220235/1170754), (-120413167012223998256572169/764369130194800000000000)]
    bernstein := [(2111975726260626713666060111/7643691301948000000000000000), (9208591601509896784563339707/30574765207792000000000000000), (37663862899051992598321534059/122299060831168000000000000000), (145308269583885004690215666383/489196243324672000000000000000), (525814725929969699756030396871/1956784973298688000000000000000)]
    reserve := (16794599723/62500000000) }

theorem quarter_019_003_valid : quarter_019_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_019_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_019_003]
  · intro i; fin_cases i <;> norm_num [quarter_019_003]
  · norm_num [quarter_019_003]
  · norm_num [quarter_019_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_019_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_019_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_019_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_019_003]

def quarter_019_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 1, 0, 0, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(231673/250000), 0, (21776787/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(592757/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-8238678976211038309129793/774005730506800000000000), (-49115626/592757), (-65109733826768638309129793/387002865253400000000000), (-49115626/592757), (-121980788677326238309129793/774005730506800000000000)]
    bernstein := [(477272706590133896248704771087/1981454670097408000000000000000), (52661339155095844167884088237/198145467009740800000000000000), (16217359561567344995261091973/59443640102922240000000000000), (519868938481048435359691749/1981454670097408000000000000), (46506272043574728661489823/198145467009740800000000000)]
    reserve := (9388309053/40000000000) }

theorem quarter_019_004_valid : quarter_019_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_019_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_019_004]
  · intro i; fin_cases i <;> norm_num [quarter_019_004]
  · norm_num [quarter_019_004]
  · norm_num [quarter_019_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_019_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_019_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_019_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_019_004]

def quarter_019_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(22406079/25000000), 0, (44660553/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(299807/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-17030661182269892909521343/1957398529634000000000000), (-44963763/599614), (-162821954872612892909521343/978699264817000000000000), (-44963763/599614), (-308613248562955892909521343/1957398529634000000000000)]
    bernstein := [(102349856194342949148331873/501094023586304000000000000), (1148422154004984670945181561/5010940235863040000000000000), (826745766726247431323963401/3496004815718400000000000000), (113485721831883046226991188473/501094023586304000000000000000), (999296720257540176098060282977/5010940235863040000000000000000)]
    reserve := (99711498563/500000000000) }

theorem quarter_019_005_valid : quarter_019_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_019_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_019_005]
  · intro i; fin_cases i <;> norm_num [quarter_019_005]
  · norm_num [quarter_019_005]
  · norm_num [quarter_019_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_019_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_019_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_019_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_019_005]

def quarter_019_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 1, 0, 0, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(345373/400000), 0, (22839737/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(37869/6250000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-1719924153567237495332851/247241475078000000000000), (-847162/12623), (-20359610527228987495332851/123620737539000000000000), (-847162/12623), (-12999765633630245831777617/82413825026000000000000)]
    bernstein := [(8102730097404880342365201953/48687552015360000000000000000), (15141896346211681502204791021/79117272024960000000000000000), (113495363872629455994497791/570557250180000000000000000), (39006384597562700060214611/206034562565000000000000000), (483828052294162560672937/2971652344687500000000000)]
    reserve := (40703621771/250000000000) }

theorem quarter_019_006_valid : quarter_019_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_019_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_019_006]
  · intro i; fin_cases i <;> norm_num [quarter_019_006]
  · norm_num [quarter_019_006]
  · norm_num [quarter_019_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_019_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_019_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_019_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_019_006]

def quarter_019_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(82830189/100000000), 0, (93207547/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(611587/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-2160864767049455192679741/399296712399400000000000), (-72452831/1223174), (-32587825353125155192679741/199648356199700000000000), (-72452831/1223174), (-63014785939200855192679741/399296712399400000000000)]
    bernstein := [(7944486300681222437123771/62390111312406250000000000), (152061772474782676498816969/998241780998500000000000000), (1917553159418961854195085037/11978901371982000000000000000), (19273738542380305840119167837/127774947967808000000000000000), (127591957454070811210055593059/1022199583742464000000000000000)]
    reserve := (15602622947/125000000000) }

theorem quarter_019_007_valid : quarter_019_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_019_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_019_007]
  · intro i; fin_cases i <;> norm_num [quarter_019_007]
  · norm_num [quarter_019_007]
  · norm_num [quarter_019_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_019_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_019_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_019_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_019_007]

def quarter_019_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 1, 0, 0, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(39545593/50000000), 0, (4742731/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(616623/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-16370826726713111514700481/4025846473026000000000000), (-31663876/616623), (-108672396249311037171566827/670974412171000000000000), (-31663876/616623), (-635663550769153111514700481/4025846473026000000000000)]
    bernstein := [(895909533610578656114937364319/10306166970946560000000000000000), (576888836997731191164562508251/5153083485473280000000000000000), (308891134286058906651146355479/2576541742736640000000000000000), (142956559643048917590240185491/1288270871368320000000000000000), (54986761533290832709388837839/644135435684160000000000000000)]
    reserve := (10670652181/125000000000) }

theorem quarter_019_008_valid : quarter_019_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_019_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_019_008]
  · intro i; fin_cases i <;> norm_num [quarter_019_008]
  · norm_num [quarter_019_008]
  · norm_num [quarter_019_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_019_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_019_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_019_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_019_008]

def quarter_019_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 1, 0, 0, 0, 2, 3]
    lambda := ![(13281573/50000000), (23262233/100000000), (11293851/100000000), (11293851/100000000), 0, 0, (689673/2500000)]
    cone := fun i => (![![(3722817/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (334533/10000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (225139/3125000), 0, 0]] i.1) i.2
    mu := ![(171309/100000000), (2041631/100000000), (3267013/50000000), (1/100000000), (2935791/100000000), (1/100000000), (225139/3125000)]
    alternative := .zero
    polynomial := [(-646963253651103594751700255580743447819/874118715687945365239505932781250000000), (-2091884012287/167950000000), (-41331032429763067703217213493040763127513/874118715687945365239505932781250000000), (-2091884012287/167950000000), (-20342034588055982054232756618730009839847/437059357843972682619752966390625000000)]
    bernstein := [(5788953401609416392784072174237226245047743/69929497255035629219160474622500000000000000), (5161619761387945642318240211295258456398227/55943597804028503375328379698000000000000000), (1623775023379032828222579985013297943690997/16783079341208551012598513909400000000000000), (172397901032675438293307121082916459910289/1790195129728912108010508150336000000000000), (6513326571569433444038120835915411128357/71607805189156484320420326013440000000000)]
    reserve := (82782711571/1000000000000) }

theorem quarter_019_009_valid : quarter_019_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_019_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_019_009]
  · intro i; fin_cases i <;> norm_num [quarter_019_009]
  · norm_num [quarter_019_009]
  · norm_num [quarter_019_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_019_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_019_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_019_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_019_009]

def quarter_019_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 1, 0, 0, 0, 2, 3]
    lambda := ![(1646669/6250000), (4727301/20000000), (11497319/100000000), (11497319/100000000), 0, 0, (27022153/100000000)]
    cone := fun i => (![![(1500999/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3405599/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1764239/25000000), 0, 0]] i.1) i.2
    mu := ![(168787/100000000), (853781/50000000), (6641557/100000000), (1/100000000), (1494341/50000000), (1/100000000), (7056957/100000000)]
    alternative := .zero
    polynomial := [(-36937001328429135207012683590320559522477663/80744426577713576048352127709784000000000000), (-85109984031129/8439350000000), (-1887076139324739838116981068212606930447597663/40372213288856788024176063854892000000000000), (-85109984031129/8439350000000), (-3737215277321050541026949452834893301372717663/80744426577713576048352127709784000000000000)]
    bernstein := [(82642218751125071176199221294205294392238381/1017628219268660946135539431074693120000000000), (191907162211631136700912548069650697725599099/2120058790143043637782373814738944000000000000), (147125661664305793652760319063943150368100168519/1550292990292100660128360852027852800000000000000), (20327774464540599099760534313768435320785572999/215318470873902869462272340559424000000000000000), (71919843655577374222740611273600617709356719737/807444265777135760483521277097840000000000000000)]
    reserve := (20302655033/250000000000) }

theorem quarter_019_010_valid : quarter_019_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_019_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_019_010]
  · intro i; fin_cases i <;> norm_num [quarter_019_010]
  · norm_num [quarter_019_010]
  · norm_num [quarter_019_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_019_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_019_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_019_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_019_010]

def quarter_019_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 3]
    lambda := ![(26099237/100000000), (2398637/10000000), (5853107/50000000), (5853107/50000000), 0, 0, (5300393/20000000)]
    cone := fun i => (![![(920521/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (138699/4000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6921107/100000000), 0, 0]] i.1) i.2
    mu := ![(166309/100000000), (1366747/100000000), (6744149/100000000), (1/100000000), (3042983/100000000), (1/100000000), (6921107/100000000)]
    alternative := .zero
    polynomial := [(-30833950816620837888900192664932452639980611/129141587004447431408094076781948000000000000), (-25991275007097/3326180000000), (-3012101373789878539510025841495839738216080611/64570793502223715704047038390974000000000000), (-25991275007097/3326180000000), (-461028368981779710856242422332826694137860047/9933968231111340877545698213996000000000000)]
    bernstein := [(102470115724708943591253612743819378854927587189/1291415870044474314080940767819480000000000000000), (35171730190257133990647087946824880361608006959/397358729244453635101827928559840000000000000000), (1916987000008136397698662074872627899214500794401/20662653920711589025295052285111680000000000000000), (586018638975800438291544642114782605221375803931/6357739667911258161629246856957440000000000000000), (28674299985038886210841179045227617671000283613709/330602462731385424404720836561786880000000000000000)]
    reserve := (39673554469/500000000000) }

theorem quarter_019_011_valid : quarter_019_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_019_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_019_011]
  · intro i; fin_cases i <;> norm_num [quarter_019_011]
  · norm_num [quarter_019_011]
  · norm_num [quarter_019_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_019_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_019_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_019_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_019_011]

def quarter_019_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 1, 0, 0, 0, 2, 3]
    lambda := ![(6455369/25000000), (12155407/50000000), (11921857/100000000), (11921857/100000000), 0, 0, (26023997/100000000)]
    cone := fun i => (![![(1620171/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3531351/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6796283/100000000), 0, 0]] i.1) i.2
    mu := ![(163869/100000000), (204201/20000000), (3420867/50000000), (1/100000000), (3099039/100000000), (1/100000000), (1699071/25000000)]
    alternative := .zero
    polynomial := [(-264553965979849664403651774809288705101/3307210892140172107584858012000000000000), (-15382371340951/2731150000000), (-704167205967106510666099788765780127577909/14882449014630774484131861054000000000000), (-15382371340951/2731150000000), (-1405953426240394374352566711558276656809909/29764898029261548968263722108000000000000)]
    bernstein := [(653227149093964140675284911460264389891242019/8466459883878840595417236510720000000000000000), (99537525832033107188954002511741932198039529/1154517256892569172102350433280000000000000000), (5161318610881087231386054334267662933931799257/57148604216182174019066346447360000000000000000), (77482160381741999609754190315230527907133843/865887942669426879076762824960000000000000000), (398789255731831790561061263129110916653822891/4762383684681847834922195537280000000000000000)]
    reserve := (38577348623/500000000000) }

theorem quarter_019_012_valid : quarter_019_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_019_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_019_012]
  · intro i; fin_cases i <;> norm_num [quarter_019_012]
  · norm_num [quarter_019_012]
  · norm_num [quarter_019_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_019_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_019_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_019_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_019_012]

def quarter_019_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 3]
    lambda := ![(25514427/100000000), (6152147/25000000), (3036337/25000000), (3036337/25000000), 0, 0, (1599143/6250000)]
    cone := fun i => (![![(1916277/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (71951/2000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3340987/50000000), 0, 0]] i.1) i.2
    mu := ![(32293/20000000), (67251/10000000), (6934177/100000000), (1/100000000), (1578567/50000000), (1/100000000), (3340987/50000000)]
    alternative := .zero
    polynomial := [(45436262625736815646437799279303827913/2036457076402939621591026021000000000000), (-7122158316577/2018312500000), (-50629047500065881254190509508424440842087/1018228538201469810795513010500000000000), (-7122158316577/2018312500000), (-101303531262757499324027456816128185512087/2036457076402939621591026021000000000000)]
    bernstein := [(24298474878795722793941595658541119116978313/325833132224470339454564163360000000000000000), (18156568942684354397945605305582419246581171/217222088149646892969709442240000000000000000), (341714839387260965889343189778162016996931339/3909997586693644073454769960320000000000000000), (1738343941611233557791678882208663590455497/20206705874385757485554366720000000000000000), (414405949550409004526655639556482902989249513/5213330115591525431273026613760000000000000000)]
    reserve := (74573370463/1000000000000) }

theorem quarter_019_013_valid : quarter_019_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_019_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_019_013]
  · intro i; fin_cases i <;> norm_num [quarter_019_013]
  · norm_num [quarter_019_013]
  · norm_num [quarter_019_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_019_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_019_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_019_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_019_013]

def quarter_019_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 1, 0, 0, 0, 2, 3]
    lambda := ![(12589709/50000000), (24878211/100000000), (6188771/50000000), (6188771/50000000), 0, 0, (25187287/100000000)]
    cone := fun i => (![![(39349/6250000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (458291/12500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6577773/100000000), 0, 0]] i.1) i.2
    mu := ![(19887/12500000), (325143/100000000), (877659/12500000), (1/100000000), (804373/25000000), (1/100000000), (6577773/100000000)]
    alternative := .zero
    polynomial := [(662801524765100452988902495803301589/9345340586150516611700127000000000000), (-18573094229/12429375000), (-21202027595193494939169930639615489397/359436176390404485065389500000000000), (-18573094229/12429375000), (-551915518999795968871407099125806025911/9345340586150516611700127000000000000)]
    bernstein := [(131423994422846677722831096206566713761453/1840313223118870963534794240000000000000000), (1203882907543724051163802832337176270239/14952544937840826578720203200000000000000), (534814293614899616778397939506644323577/6408233544788925676594372800000000000000), (750080597178572388125492359866391589/9345340586150516611700127000000000000), (662801524765100452988902495803301589/9345340586150516611700127000000000000)]
    reserve := (17730801747/250000000000) }

theorem quarter_019_014_valid : quarter_019_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_019_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_019_014]
  · intro i; fin_cases i <;> norm_num [quarter_019_014]
  · norm_num [quarter_019_014]
  · norm_num [quarter_019_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_019_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_019_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_019_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_019_014]

def quarter_019_015 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 3]
    lambda := ![(4944139/20000000), (12364211/50000000), (98083/800000), (98083/800000), 0, 0, (6507533/25000000)]
    cone := fun i => (![![0, 0, (1301303/100000000), 0, 0], ![(309057/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1815811/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1359577/20000000), 0, 0]] i.1) i.2
    mu := ![(8221/5000000), (78099/50000000), (1394841/20000000), (1/100000000), (637407/20000000), (1/100000000), (3398943/50000000)]
    alternative := .zero
    polynomial := [(45634743006045539593640003801017937/774779022626136464615868000000000000), (77328893122182681/30573899000000000), (-31074589014260707125964912134647554063/387389511313068232307934000000000000), (77328893122182681/30573899000000000), (-8884973253075351398789066324728018009/110682717518019494945124000000000000)]
    bernstein := [(45634743006045539593640003801017937/774779022626136464615868000000000000), (28941141102416772488738253457248631/387389511313068232307934000000000000), (305548553723122734608337535999640063537/3718939308605455030156166400000000000000), (50370717744396685035829072697397692231/619823218100909171692694400000000000000), (142817248083532209461781512937415205272337/1983434297922909349416622080000000000000000)]
    reserve := (29450166869/500000000000) }

theorem quarter_019_015_valid : quarter_019_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_019_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_019_015]
  · intro i; fin_cases i <;> norm_num [quarter_019_015]
  · norm_num [quarter_019_015]
  · norm_num [quarter_019_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_019_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_019_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_019_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_019_015]

def quarter_019_016 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 1, 0, 0, 0, 2, 3]
    lambda := ![(25370377/100000000), (3180229/12500000), (2494879/20000000), (2494879/20000000), 0, 0, (24239/100000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(952729/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3695017/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6330123/100000000), 0, 0]] i.1) i.2
    mu := ![(86003/12500000), (80277/50000000), (35799/500000), (1/100000000), (3242669/100000000), (1/100000000), (1582531/25000000)]
    alternative := .zero
    polynomial := [(42012632066422728203347849247802906331/1691099701330473515570560788000000000000), (3516354945691/1003462500000), (-813897576494228047960297299858588247719/16579408836573269760495694000000000000), (3516354945691/1003462500000), (-83059565434477683620153672434823804173669/1691099701330473515570560788000000000000)]
    bernstein := [(354141469707708987095651879357318440308245531/4329215235406012199860635617280000000000000000), (191318978289190220266735167692983111349900731/2164607617703006099930317808640000000000000000), (1907019066491517297630842676384775155272681/21221643310813785293434488320000000000000000), (46662433622573666453558514359087702349343531/541151904425751524982579452160000000000000000), (20958364723569903223020645756872081988251131/270575952212875762491289726080000000000000000)]
    reserve := (15491668459/200000000000) }

theorem quarter_019_016_valid : quarter_019_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_019_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_019_016]
  · intro i; fin_cases i <;> norm_num [quarter_019_016]
  · norm_num [quarter_019_016]
  · norm_num [quarter_019_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_019_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_019_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_019_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_019_016]

def quarter_019_017 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 3]
    lambda := ![(25560539/100000000), (12880507/50000000), (12492183/100000000), (12492183/100000000), 0, 0, (23694081/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(3207597/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1850143/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1237563/20000000), 0, 0]] i.1) i.2
    mu := ![(521437/50000000), (162213/100000000), (3617131/50000000), (1/100000000), (811823/25000000), (1/100000000), (773477/12500000)]
    alternative := .zero
    polynomial := [(-32989141052783471787407330155578368497/440882741025240086492519068000000000000), (3763246964411/675887500000), (-30784400377356151059935476604345051015491/661324111537860129738778602000000000000), (3763246964411/675887500000), (-61469833331553951704508731218223366925491/1322648223075720259477557204000000000000)]
    bernstein := [(18538069466870551453495391793798808484521709/211623715692115241516409152640000000000000000), (39540013977454311949376193637408073872721527/423247431384230483032818305280000000000000000), (239746094079462354392346383343840579025024943/2539484588305382898196909831680000000000000000), (51097309310557182729527049444647843410746581/564329908512307310710424407040000000000000000), (92325512264317051847428512961960938155178143/1128659817024614621420848814080000000000000000)]
    reserve := (40900504683/500000000000) }

theorem quarter_019_017_valid : quarter_019_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_019_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_019_017]
  · intro i; fin_cases i <;> norm_num [quarter_019_017]
  · norm_num [quarter_019_017]
  · norm_num [quarter_019_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_019_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_019_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_019_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_019_017]

def quarter_019_018 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 1, 0, 0, 0, 2, 3]
    lambda := ![(3213181/12500000), (26102099/100000000), (12535511/100000000), (12535511/100000000), 0, 0, (23121431/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(113329/2500000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (23207/625000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1207653/20000000), 0, 0]] i.1) i.2
    mu := ![(1388951/100000000), (819/500000), (45729/625000), (1/100000000), (651711/20000000), (1/100000000), (3019133/50000000)]
    alternative := .zero
    polynomial := [(-5235226404355034799289996899258893/22870861618111730857452000000000000), (3147489297461/409500000000), (-26652230270005610279351497216050853943/583206971261849136865026000000000000), (3147489297461/409500000000), (-4079804922568393367995323430018423411/89724149424899867210004000000000000)]
    bernstein := [(7067221783907454437818898879243325502303/76564607509247886685870080000000000000000), (73030942446096374840567517110996071641539/746504923215166895187233280000000000000000), (55213489841131419337649704654144389398839/559878692411375171390424960000000000000000), (490619301944947354538751960584767136319/5184061966771992327689120000000000000000), (1001467144008246762940832994279454037057/11664139425236982737300520000000000000000)]
    reserve := (85858639673/1000000000000) }

theorem quarter_019_018_valid : quarter_019_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_019_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_019_018]
  · intro i; fin_cases i <;> norm_num [quarter_019_018]
  · norm_num [quarter_019_018]
  · norm_num [quarter_019_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_019_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_019_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_019_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_019_018]

def quarter_019_019 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 1, 0, 0, 0, 2, 3]
    lambda := ![(25804603/100000000), (5293231/20000000), (12603629/100000000), (12603629/100000000), 0, 0, (22521983/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(294023/5000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3733297/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5881717/100000000), 0, 0]] i.1) i.2
    mu := ![(430947/25000000), (33063/20000000), (3703527/50000000), (1/100000000), (1638131/50000000), (1/100000000), (5881717/100000000)]
    alternative := .zero
    polynomial := [(-6021775916942055567942473464477852007423/13695185691878549136989691816000000000000), (16307960907059/1653150000000), (-311995728127734253384625614396958680477423/6847592845939274568494845908000000000000), (16307960907059/1653150000000), (-205989893446175483733769585109813169649141/4565061897292849712329897272000000000000)]
    bernstein := [(13216118118741693905369372908324827938937977/136951856918785491369896918160000000000000000), (11167035618740719989843326038321100806452437/109561485535028393095917534528000000000000000), (26985744903420267797956854366495291036683399/262947565284068143430202082867200000000000000), (1382459650792083680712499490892979429067581/14023870148483634316277444419584000000000000), (201335166022050047330125310175877446509513/2243819223757381490604391107133440000000000)]
    reserve := (4486439101/50000000000) }

theorem quarter_019_019_valid : quarter_019_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_019_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_019_019]
  · intro i; fin_cases i <;> norm_num [quarter_019_019]
  · norm_num [quarter_019_019]
  · norm_num [quarter_019_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_019_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_019_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_019_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_019_019]

def quarter_019_020 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 1, 0, 0, 0, 2, 3]
    lambda := ![(25857713/100000000), (268543/1000000), (6347857/50000000), (6347857/50000000), 0, 0, (21896559/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(3623951/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3760573/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (357399/6250000), 0, 0]] i.1) i.2
    mu := ![(2045413/100000000), (4169/2500000), (1876409/25000000), (1/100000000), (3300199/100000000), (1/100000000), (1143677/20000000)]
    alternative := .zero
    polynomial := [(-4473451419267537723031485955807891090579/6301839465406802758208228815200000000000), (458955170537/37900000000), (-144400278944523186491556707965357377064579/3150919732703401379104114407600000000000), (458955170537/37900000000), (-284327106469778835260081929974906863038579/6301839465406802758208228815200000000000)]
    bernstein := [(103677116671706943745550789063298153072149/1032493378012250563904836209082368000000000), (1365963346611812086091563794055648706075099/12906167225153132048810452613529600000000000), (1052120238619109141549131263786606136279967/9877168794760050037354938224640000000000000), (41308076541666770687389161567722659448597807/403317725786035376525326644172800000000000000), (94255710384786461149944204685070022374506301/1008294314465088441313316610432000000000000000)]
    reserve := (23370088731/250000000000) }

theorem quarter_019_020_valid : quarter_019_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_019_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_019_020]
  · intro i; fin_cases i <;> norm_num [quarter_019_020]
  · norm_num [quarter_019_020]
  · norm_num [quarter_019_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_019_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_019_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_019_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_019_020]

def quarter_019_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 3]
    lambda := ![(25864671/100000000), (27267697/100000000), (12810859/100000000), (12810859/100000000), 0, 0, (21245913/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(863401/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (94867/2500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1109693/20000000), 0, 0]] i.1) i.2
    mu := ![(2352079/100000000), (168139/100000000), (7612529/100000000), (1/100000000), (3330131/100000000), (1/100000000), (2774233/50000000)]
    alternative := .zero
    polynomial := [(-12425172592174410109394186522069032488128483/11920014695864727540031186295283000000000000), (7580440678337/525434375000), (-276345995856903518265335704579126395415178483/5960007347932363770015593147641500000000000), (7580440678337/525434375000), (-540266819121632626421277222636183758342228483/11920014695864727540031186295283000000000000)]
    bernstein := [(198664094803965204802597549053448764367336335277/1907202351338356406404989807245280000000000000000), (418281800674053411852778155149864817718023121913/3814404702676712812809979614490560000000000000000), (2525764170520168601749001567147616471033493077391/22886428216060276876859877686943360000000000000000), (1620698541067061646548756447747283990362515088593/15257618810706851251239918457962240000000000000000), (2965326802262288628218957947515197907973192397917/30515237621413702502479836915924480000000000000000)]
    reserve := (4858764069/50000000000) }

theorem quarter_019_021_valid : quarter_019_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_019_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_019_021]
  · intro i; fin_cases i <;> norm_num [quarter_019_021]
  · norm_num [quarter_019_021]
  · norm_num [quarter_019_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_019_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_019_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_019_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_019_021]

def quarter_019_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 1, 0, 0, 0, 2, 3]
    lambda := ![(2582553/10000000), (865861/3125000), (3237017/25000000), (3237017/25000000), 0, 0, (10285391/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(10037453/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3835323/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (671519/12500000), 0, 0]] i.1) i.2
    mu := ![(2642209/100000000), (10591/6250000), (3863941/50000000), (1/100000000), (1682899/50000000), (1/100000000), (671519/12500000)]
    alternative := .zero
    polynomial := [(-4224746273828817287173539123833194555057069/2932663413542325603578261452776000000000000), (104810638167/6230000000), (-9870260310172363577832043641643475927293867/209475958110166114541304389484000000000000), (104810638167/6230000000), (-133958898068584272802475071859175468427057069/2932663413542325603578261452776000000000000)]
    bernstein := [(47626642232628141115337814113142803129404642243/441624608156961973244726430535680000000000000000), (2087763472099111694110394121221945065604037183/18401025339873415551863601272320000000000000000), (1435473893346720336957650315395212160371733019/12568557486609966872478263369040000000000000000), (268930765111711770087754989461974107971809107/2443886177951938002981884543980000000000000000), (46223505709904287398482206480177305565355339/458228658365988375559103351996250000000000000)]
    reserve := (100874323039/1000000000000) }

theorem quarter_019_022_valid : quarter_019_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_019_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_019_022]
  · intro i; fin_cases i <;> norm_num [quarter_019_022]
  · norm_num [quarter_019_022]
  · norm_num [quarter_019_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_019_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_019_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_019_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_019_022]

def quarter_019_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 3]
    lambda := ![0, (10491247/20000000), (23771883/100000000), (23771883/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(23726859/100000000), 0, (5990433/12500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (440089/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (63567/20000000), (3638043/25000000), (1/100000000), (1544851/25000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-91522601557173648216339319/25203628781743720000000000), (124325274115107/3531500000000), (-3264751932096707703712357157/37805443172615580000000000), (124325274115107/3531500000000), (-6254936059521894462775696357/75610886345231160000000000)]
    bernstein := [(1235964657144135851506516267/11814200991442368750000000000), (2038276898290092061588482821/17184292351188900000000000000), (1858907054311770682932489481/15022030399714800000000000000), (87905614234093052487917022359/733196473650726400000000000000), (6897603499633330876582964208041/64521289681263923200000000000000)]
    reserve := (52308431947/500000000000) }

theorem quarter_019_023_valid : quarter_019_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_019_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_019_023]
  · intro i; fin_cases i <;> norm_num [quarter_019_023]
  · norm_num [quarter_019_023]
  · norm_num [quarter_019_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_019_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_019_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_019_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_019_023]

def quarter_019_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 1, 0, 0, 0, 2, 3]
    lambda := ![0, (53874957/100000000), (23062521/100000000), (23062521/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(26630293/100000000), 0, (12030427/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3415653/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (161521/50000000), (14807977/100000000), (1/100000000), (5995009/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-200864227258375760836734089210903/43016574144090576459000000000000), (3262695357022683/80760500000000), (-1926999407788365499641526551020903/21508287072045288229500000000000), (3262695357022683/80760500000000), (-3653134588318355238446319012830903/43016574144090576459000000000000)]
    bernstein := [(14020982959092214274493725589850947817/110122429808871875735040000000000000000), (1563770987500650171985681649574523633/11012242980887187573504000000000000000), (487308409008303141296052765901727803/3303672894266156272051200000000000000), (15823194565932059746573544199209681/110122429808871875735040000000000000), (1435729986841308497677871769061033/11012242980887187573504000000000000)]
    reserve := (63660886267/500000000000) }

theorem quarter_019_024_valid : quarter_019_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_019_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_019_024]
  · intro i; fin_cases i <;> norm_num [quarter_019_024]
  · norm_num [quarter_019_024]
  · norm_num [quarter_019_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_019_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_019_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_019_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_019_024]

def quarter_019_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 3]
    lambda := ![0, (27631693/50000000), (22368307/100000000), (22368307/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(7387469/25000000), 0, (1203459/2500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3312837/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (163789/50000000), (15064439/100000000), (1/100000000), (5814551/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-6821417524347967874024727621943/1163250932392057899000000000000), (375002941283947/8189450000000), (-54055715801945626553488971021943/581625466196028949500000000000), (375002941283947/8189450000000), (-101290014079543285232953214421943/1163250932392057899000000000000)]
    bernstein := [(44759407462582567387258890378473/297792238692366822144000000000000), (8657442306486637931078644460907/52244252402169617920000000000000), (15331467355525430363857983420383123/89337671607710046643200000000000000), (876908666018130331728851099928291/5224425240216961792000000000000000), (459259768655299314698292903847522937/2977922386923668221440000000000000000)]
    reserve := (30060828757/200000000000) }

theorem quarter_019_025_valid : quarter_019_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_019_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_019_025]
  · intro i; fin_cases i <;> norm_num [quarter_019_025]
  · norm_num [quarter_019_025]
  · norm_num [quarter_019_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_019_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_019_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_019_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_019_025]

def quarter_019_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 1, 0, 0, 0, 2, 3]
    lambda := ![0, (442279/781250), (338971/1562500), (338971/1562500), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1298597/4000000), 0, (2398379/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6425981/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2589/781250), (7659499/50000000), (1/100000000), (1127861/20000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1291930438926933224673566333977/178927865376346968000000000000), (2216300316389/43150000000), (-2874292381062509639517721844659/29821310896057828000000000000), (2216300316389/43150000000), (-15953823847448124612432764733977/178927865376346968000000000000)]
    bernstein := [(26500134273467877986152557777342781/152685111787816079360000000000000000), (21726798716428920603162804165877439/114513833840862059520000000000000000), (5612909641458511741010488900520347/28628458460215514880000000000000000), (1376795173841122553758957276487531/7157114615053878720000000000000000), (319268209929382399190706597219263/1789278653763469680000000000000000)]
    reserve := (173560696017/1000000000000) }

theorem quarter_019_026_valid : quarter_019_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_019_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_019_026]
  · intro i; fin_cases i <;> norm_num [quarter_019_026]
  · norm_num [quarter_019_026]
  · norm_num [quarter_019_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_019_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_019_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_019_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_019_026]

def quarter_019_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 1, 0, 0, 0, 2, 3]
    lambda := ![0, (1447741/2500000), (1052259/5000000), (1052259/5000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(8838433/25000000), 0, (47605433/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6233753/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (167219/50000000), (7784457/50000000), (1/100000000), (5470609/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-33202198401267665860309670516121/3797942186856050958400000000000), (954740609211387/16721900000000), (-189736716665527990413233776596121/1898971093428025479200000000000), (954740609211387/16721900000000), (-346271234929788314966157882676121/3797942186856050958400000000000)]
    bernstein := [(7485000203682858547032473633646399/37979421868560509584000000000000000), (32517745513971879228719150998654029/151917687474242038336000000000000000), (402580883570592038237752837572242177/1823012249690904460032000000000000000), (40616543064055849603545113381076653/186975615352913277952000000000000000), (1973689211263731000126116028511471319/9722731998351490453504000000000000000)]
    reserve := (197080414483/1000000000000) }

theorem quarter_019_027_valid : quarter_019_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_019_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_019_027]
  · intro i; fin_cases i <;> norm_num [quarter_019_027]
  · norm_num [quarter_019_027]
  · norm_num [quarter_019_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_019_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_019_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_019_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_019_027]

def quarter_019_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 1, 0, 0, 0, 2, 3]
    lambda := ![0, (462083/781250), (319167/1562500), (319167/1562500), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(19096959/50000000), 0, (11762537/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (121011/2000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (336677/100000000), (7905667/50000000), (1/100000000), (1061967/20000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-35740294053701733533061011971/3426171031895097640000000000), (82808532671399/1315144531250), (-177338108189709254314797255171/1713085515947548820000000000), (82808532671399/1315144531250), (-318935922325716775096533498371/3426171031895097640000000000)]
    bernstein := [(1937028073880658348488252040619469/8770997841651449958400000000000000), (1046562680635799224570887220343591/4385498920825724979200000000000000), (539207991622645946794906833734949/2192749460412862489600000000000000), (1102779576270763195532928775871/4549272739445772800000000000000), (124924920533752048260995743656829/548187365103215622400000000000000)]
    reserve := (27605583037/125000000000) }

theorem quarter_019_028_valid : quarter_019_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_019_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_019_028]
  · intro i; fin_cases i <;> norm_num [quarter_019_028]
  · norm_num [quarter_019_028]
  · norm_num [quarter_019_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_019_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_019_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_019_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_019_028]

def quarter_019_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 1, 0, 0, 0, 2, 3]
    lambda := ![0, (60312151/100000000), (4960981/25000000), (4960981/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(40962871/100000000), 0, (46302341/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5877931/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (84519/25000000), (16043363/100000000), (1/100000000), (5158347/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-91687146745926825344881620201299/7460862517136877609600000000000), (15539527813621643/225384000000000), (-399830260632341639650408442669299/3730431258568438804800000000000), (15539527813621643/225384000000000), (-78663708279861828217326140570811/828984724126319734400000000000)]
    bernstein := [(292259686510284861677971006880896301/1193738002741900417536000000000000000), (41936859269511776296985842504494923/159165067032253389004800000000000000), (155421557592774676173316340060198399/572994241316112200417280000000000000), (20465095249981495171559876748719113/76399232175481626722304000000000000), (7733781157205017625837313749564029/30559692870192650688921600000000000)]
    reserve := (24482732881/100000000000) }

theorem quarter_019_029_valid : quarter_019_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_019_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_019_029]
  · intro i; fin_cases i <;> norm_num [quarter_019_029]
  · norm_num [quarter_019_029]
  · norm_num [quarter_019_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_019_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_019_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_019_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_019_029]

def quarterTable019 : OwnerTable where
  mode := .quarter
  owners := ![0, 1, 0, 0, 0, 2, 3]
  rows := [quarter_019_000, quarter_019_001, quarter_019_002, quarter_019_003, quarter_019_004, quarter_019_005, quarter_019_006, quarter_019_007, quarter_019_008, quarter_019_009, quarter_019_010, quarter_019_011, quarter_019_012, quarter_019_013, quarter_019_014, quarter_019_015, quarter_019_016, quarter_019_017, quarter_019_018, quarter_019_019, quarter_019_020, quarter_019_021, quarter_019_022, quarter_019_023, quarter_019_024, quarter_019_025, quarter_019_026, quarter_019_027, quarter_019_028, quarter_019_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_019_000_valid
    · exact quarter_019_001_valid
    · exact quarter_019_002_valid
    · exact quarter_019_003_valid
    · exact quarter_019_004_valid
    · exact quarter_019_005_valid
    · exact quarter_019_006_valid
    · exact quarter_019_007_valid
    · exact quarter_019_008_valid
    · exact quarter_019_009_valid
    · exact quarter_019_010_valid
    · exact quarter_019_011_valid
    · exact quarter_019_012_valid
    · exact quarter_019_013_valid
    · exact quarter_019_014_valid
    · exact quarter_019_015_valid
    · exact quarter_019_016_valid
    · exact quarter_019_017_valid
    · exact quarter_019_018_valid
    · exact quarter_019_019_valid
    · exact quarter_019_020_valid
    · exact quarter_019_021_valid
    · exact quarter_019_022_valid
    · exact quarter_019_023_valid
    · exact quarter_019_024_valid
    · exact quarter_019_025_valid
    · exact quarter_019_026_valid
    · exact quarter_019_027_valid
    · exact quarter_019_028_valid
    · exact quarter_019_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
