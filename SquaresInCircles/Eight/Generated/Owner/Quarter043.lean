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

def quarter_043_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 3, 0, 0, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(102465129/100000000), 0, (19192791/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(560543/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-9336687063886503438164777/457463486508250000000000), (-64079547/560543), (-40663458022347003438164777/228731743254125000000000), (-64079547/560543), (-71990228980807503438164777/457463486508250000000000)]
    bernstein := [(703685342559292178019903367/1873770440737792000000000000), (1875854259774222321528801499/4684426101844480000000000000), (14277826683957307031840585677/35133195763833600000000000000), (11531305198752544833786737987/29277663136528000000000000000), (26588901590914354362542792023/73194157841320000000000000000)]
    reserve := (36326535307/100000000000) }

theorem quarter_043_000_valid : quarter_043_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_043_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_043_000]
  · intro i; fin_cases i <;> norm_num [quarter_043_000]
  · norm_num [quarter_043_000]
  · norm_num [quarter_043_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_043_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_043_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_043_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_043_000]

def quarter_043_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(100371721/100000000), 0, (19887081/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(71153/12500000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-8208487042318949692827207/464548117886000000000000), (-60597559/569224), (-40668488900274449692827207/232274058943000000000000), (-60597559/569224), (-73128490758229949692827207/464548117886000000000000)]
    bernstein := [(25542887225243746976342241593/74327698861760000000000000000), (54783549554092372087240394787/148655397723520000000000000000), (111418677708706730449600452033/297310795447040000000000000000), (215717198152734591859305697947/594621590894080000000000000000), (396003581849212929304558675273/1189243181788160000000000000000)]
    reserve := (83246973351/250000000000) }

theorem quarter_043_001_valid : quarter_043_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_043_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_043_001]
  · intro i; fin_cases i <;> norm_num [quarter_043_001]
  · norm_num [quarter_043_001]
  · norm_num [quarter_043_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_043_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_043_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_043_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_043_001]

def quarter_043_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 3, 0, 0, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(19608541/20000000), 0, (41103203/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(577517/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-1426099006298046362438957/94263219891350000000000), (-56939502/577517), (-8135027509922696362438957/47131609945675000000000), (-56939502/577517), (-14843956013547346362438957/94263219891350000000000)]
    bernstein := [(74943659209813187891663083523/241313842921856000000000000000), (20236252696962981297167944413/60328460730464000000000000000), (15471642832850517916961408309/45246345547848000000000000000), (1246171032223673960933468593/3770528795654000000000000000), (284174818686034867862751883/942632198913500000000000000)]
    reserve := (301469458621/1000000000000) }

theorem quarter_043_002_valid : quarter_043_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_043_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_043_002]
  · intro i; fin_cases i <;> norm_num [quarter_043_002]
  · norm_num [quarter_043_002]
  · norm_num [quarter_043_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_043_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_043_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_043_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_043_002]

def quarter_043_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(47737769/50000000), 0, (84730841/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(585377/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-9773973405635598256572169/764369130194800000000000), (-106220235/1170754), (-65093570208929798256572169/382184565097400000000000), (-106220235/1170754), (-120413167012223998256572169/764369130194800000000000)]
    bernstein := [(2111975726260626713666060111/7643691301948000000000000000), (9208591601509896784563339707/30574765207792000000000000000), (37663862899051992598321534059/122299060831168000000000000000), (145308269583885004690215666383/489196243324672000000000000000), (525814725929969699756030396871/1956784973298688000000000000000)]
    reserve := (16794599723/62500000000) }

theorem quarter_043_003_valid : quarter_043_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_043_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_043_003]
  · intro i; fin_cases i <;> norm_num [quarter_043_003]
  · norm_num [quarter_043_003]
  · norm_num [quarter_043_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_043_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_043_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_043_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_043_003]

def quarter_043_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 3, 0, 0, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(231673/250000), 0, (21776787/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(592757/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-8238678976211038309129793/774005730506800000000000), (-49115626/592757), (-65109733826768638309129793/387002865253400000000000), (-49115626/592757), (-121980788677326238309129793/774005730506800000000000)]
    bernstein := [(477272706590133896248704771087/1981454670097408000000000000000), (52661339155095844167884088237/198145467009740800000000000000), (16217359561567344995261091973/59443640102922240000000000000), (519868938481048435359691749/1981454670097408000000000000), (46506272043574728661489823/198145467009740800000000000)]
    reserve := (9388309053/40000000000) }

theorem quarter_043_004_valid : quarter_043_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_043_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_043_004]
  · intro i; fin_cases i <;> norm_num [quarter_043_004]
  · norm_num [quarter_043_004]
  · norm_num [quarter_043_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_043_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_043_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_043_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_043_004]

def quarter_043_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(22406079/25000000), 0, (44660553/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(299807/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-17030661182269892909521343/1957398529634000000000000), (-44963763/599614), (-162821954872612892909521343/978699264817000000000000), (-44963763/599614), (-308613248562955892909521343/1957398529634000000000000)]
    bernstein := [(102349856194342949148331873/501094023586304000000000000), (1148422154004984670945181561/5010940235863040000000000000), (826745766726247431323963401/3496004815718400000000000000), (113485721831883046226991188473/501094023586304000000000000000), (999296720257540176098060282977/5010940235863040000000000000000)]
    reserve := (99711498563/500000000000) }

theorem quarter_043_005_valid : quarter_043_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_043_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_043_005]
  · intro i; fin_cases i <;> norm_num [quarter_043_005]
  · norm_num [quarter_043_005]
  · norm_num [quarter_043_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_043_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_043_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_043_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_043_005]

def quarter_043_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 3, 0, 0, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(345373/400000), 0, (22839737/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(37869/6250000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-1719924153567237495332851/247241475078000000000000), (-847162/12623), (-20359610527228987495332851/123620737539000000000000), (-847162/12623), (-12999765633630245831777617/82413825026000000000000)]
    bernstein := [(8102730097404880342365201953/48687552015360000000000000000), (15141896346211681502204791021/79117272024960000000000000000), (113495363872629455994497791/570557250180000000000000000), (39006384597562700060214611/206034562565000000000000000), (483828052294162560672937/2971652344687500000000000)]
    reserve := (40703621771/250000000000) }

theorem quarter_043_006_valid : quarter_043_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_043_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_043_006]
  · intro i; fin_cases i <;> norm_num [quarter_043_006]
  · norm_num [quarter_043_006]
  · norm_num [quarter_043_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_043_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_043_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_043_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_043_006]

def quarter_043_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(82830189/100000000), 0, (93207547/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(611587/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-2160864767049455192679741/399296712399400000000000), (-72452831/1223174), (-32587825353125155192679741/199648356199700000000000), (-72452831/1223174), (-63014785939200855192679741/399296712399400000000000)]
    bernstein := [(7944486300681222437123771/62390111312406250000000000), (152061772474782676498816969/998241780998500000000000000), (1917553159418961854195085037/11978901371982000000000000000), (19273738542380305840119167837/127774947967808000000000000000), (127591957454070811210055593059/1022199583742464000000000000000)]
    reserve := (15602622947/125000000000) }

theorem quarter_043_007_valid : quarter_043_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_043_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_043_007]
  · intro i; fin_cases i <;> norm_num [quarter_043_007]
  · norm_num [quarter_043_007]
  · norm_num [quarter_043_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_043_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_043_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_043_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_043_007]

def quarter_043_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 3, 0, 0, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(39545593/50000000), 0, (4742731/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(616623/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-16370826726713111514700481/4025846473026000000000000), (-31663876/616623), (-108672396249311037171566827/670974412171000000000000), (-31663876/616623), (-635663550769153111514700481/4025846473026000000000000)]
    bernstein := [(895909533610578656114937364319/10306166970946560000000000000000), (576888836997731191164562508251/5153083485473280000000000000000), (308891134286058906651146355479/2576541742736640000000000000000), (142956559643048917590240185491/1288270871368320000000000000000), (54986761533290832709388837839/644135435684160000000000000000)]
    reserve := (10670652181/125000000000) }

theorem quarter_043_008_valid : quarter_043_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_043_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_043_008]
  · intro i; fin_cases i <;> norm_num [quarter_043_008]
  · norm_num [quarter_043_008]
  · norm_num [quarter_043_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_043_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_043_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_043_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_043_008]

def quarter_043_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 3, 0, 0, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(37567091/50000000), 0, (96288913/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(31049/5000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-1184167566567073451240173/405429272476000000000000), (-53979451/1241960), (-32617018821917373451240173/202714636238000000000000), (-53979451/1241960), (-64049870077267673451240173/405429272476000000000000)]
    bernstein := [(2927336486117451403092620387/64868683596160000000000000000), (1820627760169226926171386609/25947473438464000000000000000), (812258446596766015593229307/10378989375385600000000000000), (57798138851086416822073413/830319150030848000000000000), (48298632683532897383783/1088943147581440000000000)]
    reserve := (554420963/12500000000) }

theorem quarter_043_009_valid : quarter_043_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_043_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_043_009]
  · intro i; fin_cases i <;> norm_num [quarter_043_009]
  · norm_num [quarter_043_009]
  · norm_num [quarter_043_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_043_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_043_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_043_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_043_009]

def quarter_043_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 3, 0, 0, 0, 2, 3]
    lambda := ![(3683139/25000000), (4411777/20000000), (93942/390625), (93942/390625), 0, 0, (7555127/50000000)]
    cone := fun i => (![![(839329/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3561777/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3946111/100000000), 0, 0]] i.1) i.2
    mu := ![(94383/100000000), (104729/1562500), (382203/25000000), (1/100000000), (6251479/100000000), (1/100000000), (3946111/100000000)]
    alternative := .zero
    polynomial := [(-1009429341572732860603352682306130915147/4248344884541971925387358384000000000000), (-27446932502087/4719150000000), (-58481241895914594472325347441488267875147/2124172442270985962693679192000000000000), (-27446932502087/4719150000000), (-38651018150085485361349114066890134945049/1416114961513990641795786128000000000000)]
    bernstein := [(789831834557984126122957486182029142559/12355896317456035744179848478720000000000), (23498153787058314302623018584618250241093/334638858597767634738204229632000000000000), (6004091106391748521692761575518223341341011/81568221783205860967437280972800000000000000), (2519111529238800227699655004406981561902393/33986759076335775403098867072000000000000000), (9147859557017622648106788787906906471596359/127450346536259157761620751520000000000000000)]
    reserve := (63923475421/1000000000000) }

theorem quarter_043_010_valid : quarter_043_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_043_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_043_010]
  · intro i; fin_cases i <;> norm_num [quarter_043_010]
  · norm_num [quarter_043_010]
  · norm_num [quarter_043_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_043_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_043_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_043_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_043_010]

def quarter_043_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 3]
    lambda := ![(566327/4000000), (1135159/5000000), (24381/100000), (24381/100000), 0, 0, (2875329/20000000)]
    cone := fun i => (![![(2496797/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (144437/2000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (150181/4000000), 0, 0]] i.1) i.2
    mu := ![(90219/100000000), (6760729/100000000), (251347/20000000), (1/100000000), (3168871/50000000), (1/100000000), (1877263/50000000)]
    alternative := .zero
    polynomial := [(-96461277729723517344771626820766827439133/912000178635166618822031102481000000000000), (-156831688231/35380000000), (-12392922546956969212529915085438895240564133/456000089317583309411015551240500000000000), (-156831688231/35380000000), (-24689383816184214907715058544057023653689133/912000178635166618822031102481000000000000)]
    bernstein := [(615234668080546459313643607598320883551654267/9120001786351666188220311024810000000000000000), (2683926504214532200920154836594853847609594501/36480007145406664752881244099240000000000000000), (33630252043057877758906771248461789117772632509/437760085744879977034574929190880000000000000000), (45082137374918525577464877945617305393349681209/583680114326506636046099905587840000000000000000), (174706553287328486590780526743668016300049669827/2334720457306026544184399622351360000000000000000)]
    reserve := (67459928461/1000000000000) }

theorem quarter_043_011_valid : quarter_043_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_043_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_043_011]
  · intro i; fin_cases i <;> norm_num [quarter_043_011]
  · norm_num [quarter_043_011]
  · norm_num [quarter_043_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_043_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_043_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_043_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_043_011]

def quarter_043_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 3, 0, 0, 0, 2, 3]
    lambda := ![(13574113/100000000), (11692203/50000000), (6170113/25000000), (6170113/25000000), 0, 0, (213759/1562500)]
    cone := fun i => (![![(851709/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (146211/2000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (446593/12500000), 0, 0]] i.1) i.2
    mu := ![(17229/20000000), (6832119/100000000), (7541/781250), (1/100000000), (6415583/100000000), (1/100000000), (446593/12500000)]
    alternative := .zero
    polynomial := [(-138018541338065248982937900827942111/11136376702220107326769816000000000000), (-2277719893209/717875000000), (-153463866140061726993463773741649926611/5568188351110053663384908000000000000), (-2277719893209/717875000000), (-306789713738785388737944609582471911111/11136376702220107326769816000000000000)]
    bernstein := [(2024392690823969993604051294627576169763209/28509124357683474756530728960000000000000000), (1097207478444015611171048900468747142908003/14254562178841737378265364480000000000000000), (1711461579687269321368286320395507920237203/21381843268262606067398046720000000000000000), (285945145742466760604096716859587099044667/3563640544710434344566341120000000000000000), (138219523329699867422525396303471394320089/1781820272355217172283170560000000000000000)]
    reserve := (71008588879/1000000000000) }

theorem quarter_043_012_valid : quarter_043_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_043_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_043_012]
  · intro i; fin_cases i <;> norm_num [quarter_043_012]
  · norm_num [quarter_043_012]
  · norm_num [quarter_043_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_043_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_043_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_043_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_043_012]

def quarter_043_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 3]
    lambda := ![(648849/5000000), (24110197/100000000), (24949647/100000000), (24949647/100000000), 0, 0, (13013529/100000000)]
    cone := fun i => (![![(243661/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (7390287/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3398541/100000000), 0, 0]] i.1) i.2
    mu := ![(20531/25000000), (6918559/100000000), (130859/20000000), (1/100000000), (6485559/100000000), (1/100000000), (1699271/50000000)]
    alternative := .zero
    polynomial := [(263630297871502858717580754316099965017/5574193825254193042717107028000000000000), (-4160902398883/2053100000000), (-82672852585513035869505707544247758962983/2787096912627096521358553514000000000000), (-4160902398883/2053100000000), (-165609335468897574597728995842811617890983/5574193825254193042717107028000000000000)]
    bernstein := [(9496876785083960935747325043861202836463231/127410144577238698119248160640000000000000000), (143427760996927671035004007884443855892969417/1783742024081341773669474248960000000000000000), (890168420137213162140037497917452307895055451/10702452144488050642016845493760000000000000000), (591137933084507359270748136508032746554109817/7134968096325367094677896995840000000000000000), (1133628646215166527787515227118549368545683417/14269936192650734189355793991680000000000000000)]
    reserve := (74537838541/1000000000000) }

theorem quarter_043_013_valid : quarter_043_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_043_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_043_013]
  · intro i; fin_cases i <;> norm_num [quarter_043_013]
  · norm_num [quarter_043_013]
  · norm_num [quarter_043_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_043_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_043_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_043_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_043_013]

def quarter_043_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 3, 0, 0, 0, 2, 3]
    lambda := ![(12362457/100000000), (2488931/10000000), (6297739/25000000), (6297739/25000000), 0, 0, (12366321/100000000)]
    cone := fun i => (![![(30911/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1492353/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (40369/1250000), 0, 0]] i.1) i.2
    mu := ![(78113/100000000), (3511043/50000000), (81327/25000000), (1/100000000), (6548287/100000000), (1/100000000), (3229521/100000000)]
    alternative := .zero
    polynomial := [(16222716030760107031574336680698871986043/209641625544549216696755436716000000000000), (-771091082837/781130000000), (-12166625568850574697801850305208844082901871/314462438316823825045133155074000000000000), (-771091082837/781130000000), (-24381919285793429716698423620459784781761871/628924876633647650090266310148000000000000)]
    bernstein := [(125391601376074495595262078211363491679750490929/1610047684182137984231081753978880000000000000000), (12047364809313490958394147297947175946948147/143754257516262320020632299462400000000000000), (258691009321044847308386828912362328828117329/3018839407841508720433278288710400000000000000), (17516137004612533446557608590959546163543/209641625544549216696755436716000000000000), (16222716030760107031574336680698871986043/209641625544549216696755436716000000000000)]
    reserve := (77383086439/1000000000000) }

theorem quarter_043_014_valid : quarter_043_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_043_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_043_014]
  · intro i; fin_cases i <;> norm_num [quarter_043_014]
  · norm_num [quarter_043_014]
  · norm_num [quarter_043_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_043_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_043_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_043_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_043_014]

def quarter_043_015 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 3]
    lambda := ![(11644291/100000000), (25370161/100000000), (12681117/50000000), (12681117/50000000), 0, 0, (306527/2500000)]
    cone := fun i => (![![0, 0, (306479/50000000), 0, 0], ![0, 0, 0, 0, 0], ![(126831/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (7512499/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (800509/25000000), 0, 0]] i.1) i.2
    mu := ![(9681/12500000), (1410701/20000000), (160251/100000000), (1/100000000), (659281/10000000), (1/100000000), (800509/25000000)]
    alternative := .zero
    polynomial := [(119677134624332119997070740700437297/1611761459487091528141624000000000000), (1281287996038513/738757110000000), (-1867175450452028568025081708761767465417/31429348459998284798761668000000000000), (1281287996038513/738757110000000), (-3739018309154406088730049176410851985417/62858696919996569597523336000000000000)]
    bernstein := [(119677134624332119997070740700437297/1611761459487091528141624000000000000), (764112852141192031631186950306801369/8979813845713795656789048000000000000), (27077648611761103094139038692733422532983/301721745215983534068112012800000000000000), (8871991362090014510689903931897014422383/100573915071994511356037337600000000000000), (4317191420672911509299223048225797247720061/53639421371730406056553246720000000000000000)]
    reserve := (1160193537/15625000000) }

theorem quarter_043_015_valid : quarter_043_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_043_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_043_015]
  · intro i; fin_cases i <;> norm_num [quarter_043_015]
  · norm_num [quarter_043_015]
  · norm_num [quarter_043_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_043_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_043_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_043_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_043_015]

def quarter_043_016 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 3, 0, 0, 0, 2, 3]
    lambda := ![(2216071/20000000), (26162339/100000000), (26088861/100000000), (26088861/100000000), 0, 0, (2115917/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(97971/5000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1931933/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1381453/50000000), 0, 0]] i.1) i.2
    mu := ![(150557/50000000), (7179147/100000000), (1651/1000000), (1/100000000), (6781693/100000000), (1/100000000), (1381453/50000000)]
    alternative := .zero
    polynomial := [(16866002957624992781374524262624781579/451849064379733961375856993000000000000), (2737819462519/825500000000), (-10202696584751430597485436351874088995771/225924532189866980687928496500000000000), (2737819462519/825500000000), (-1570943013266191245211711325231600213317/34757620336902612413527461000000000000)]
    bernstein := [(106477241076530846495292858581252859614359679/1156733604812118941122193902080000000000000000), (487841056291936166121693460597431469663987/4943306003470593765479461120000000000000000), (87300363384074034315661563518762929110411437/867550203609089205841645426560000000000000000), (120949611835011035942689186692089944439587/1235826500867648441369865280000000000000000), (6534625311952374284535017194737269017930079/72295850300757433820137118880000000000000000)]
    reserve := (90387280663/1000000000000) }

theorem quarter_043_016_valid : quarter_043_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_043_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_043_016]
  · intro i; fin_cases i <;> norm_num [quarter_043_016]
  · norm_num [quarter_043_016]
  · norm_num [quarter_043_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_043_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_043_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_043_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_043_016]

def quarter_043_017 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 3]
    lambda := ![(10447407/100000000), (13383271/50000000), (13279121/50000000), (13279121/50000000), 0, 0, (151087/1562500)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(3332799/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3933383/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2525251/100000000), 0, 0]] i.1) i.2
    mu := ![(213859/50000000), (3630151/50000000), (33709/20000000), (1/100000000), (6903707/100000000), (1/100000000), (2525251/100000000)]
    alternative := .zero
    polynomial := [(-2230782811135103765724118783964625069411/36498497039442997078846365217360000000000), (46233509544089/8427250000000), (-815031953377668366525833104920255764257571/18249248519721498539423182608680000000000), (46233509544089/8427250000000), (-1627833123944201629285942091056546903445731/36498497039442997078846365217360000000000)]
    bernstein := [(595328140350748261550211013307790385163662269/5839759526310879532615418434777600000000000000), (97422672327284420416261500321435140634929539/898424542509366081940833605350400000000000000), (406795265828436586700044419657830865070379077/3688269174512134441651843221964800000000000000), (5022281696875563375848091586439900978975500463/46718076210487036260923347478220800000000000000), (9346326778496548335110102882230232135715030189/93436152420974072521846694956441600000000000000)]
    reserve := (50014510103/500000000000) }

theorem quarter_043_017_valid : quarter_043_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_043_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_043_017]
  · intro i; fin_cases i <;> norm_num [quarter_043_017]
  · norm_num [quarter_043_017]
  · norm_num [quarter_043_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_043_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_043_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_043_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_043_017]

def quarter_043_018 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 3, 0, 0, 0, 2, 3]
    lambda := ![(9822107/100000000), (27400489/100000000), (26984107/100000000), (26984107/100000000), 0, 0, (880919/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1189663/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (7992911/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2300559/100000000), 0, 0]] i.1) i.2
    mu := ![(533193/100000000), (114921/1562500), (42987/25000000), (1/100000000), (7014409/100000000), (1/100000000), (28757/1250000)]
    alternative := .zero
    polynomial := [(-103296395526040647793513368977581011751/472283870015954627206495416000000000000), (374772014003/48300000000), (-10640621192565089493920416496422951641751/236141935007977313603247708000000000000), (374772014003/48300000000), (-21177945989604138340047319623868322271751/472283870015954627206495416000000000000)]
    bernstein := [(134951283555693989077235089820172832975799369/1209046707240843845648628264960000000000000000), (35731766683605307659819065882227028896314323/302261676810210961412157066240000000000000000), (27235710878849899867184295188194440129800423/226696257607658221059117799680000000000000000), (2217415145087720766792081771236705412119047/18891354800638185088259816640000000000000000), (518950525215863476134396110899258837468049/4722838700159546272064954160000000000000000)]
    reserve := (109881060557/1000000000000) }

theorem quarter_043_018_valid : quarter_043_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_043_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_043_018]
  · intro i; fin_cases i <;> norm_num [quarter_043_018]
  · norm_num [quarter_043_018]
  · norm_num [quarter_043_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_043_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_043_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_043_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_043_018]

def quarter_043_019 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 3, 0, 0, 0, 2, 3]
    lambda := ![(9202931/100000000), (28068587/100000000), (27366981/100000000), (27366981/100000000), 0, 0, (7994521/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(6236501/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8106321/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (417561/20000000), 0, 0]] i.1) i.2
    mu := ![(618309/100000000), (7463859/100000000), (43831/25000000), (1/100000000), (1422787/20000000), (1/100000000), (417561/20000000)]
    alternative := .zero
    polynomial := [(-23491504607573413718284985426283778508443/53410626598688269396747821612000000000000), (35570606738739/3506480000000), (-1225316532552919048876125587559592488903443/26705313299344134698373910806000000000000), (35570606738739/3506480000000), (-809047186832754894677988729897633733099481/17803542199562756465582607204000000000000)]
    bernstein := [(12109717176045475597410721430029168931269/99776997195382532032034040000000000000000), (542278664200070242930963547015916156251117/4230544681084219358158243296000000000000000), (133568492905344599515050046993704812676182659/1025484030694814772417558174950400000000000000), (536570348590514101921006712358592244633117/4207113972081291374020751486976000000000000), (80777553977169969603196223503039395792241/673138235533006619843320237916160000000000)]
    reserve := (120001434643/1000000000000) }

theorem quarter_043_019_valid : quarter_043_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_043_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_043_019]
  · intro i; fin_cases i <;> norm_num [quarter_043_019]
  · norm_num [quarter_043_019]
  · norm_num [quarter_043_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_043_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_043_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_043_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_043_019]

def quarter_043_020 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 3, 0, 0, 0, 2, 3]
    lambda := ![0, (1708947/5000000), (3291053/10000000), (3291053/10000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (10124079/100000000), 0, 0], ![(4612401/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1949673/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2221169/25000000), (42449/20000000), (1/100000000), (4277479/50000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-337442807510334332325344389521/379584101937898352000000000000), (7882348851747/530612500000), (-10395961260017558030662217989521/189792050968949176000000000000), (7882348851747/530612500000), (-20454479712524781728999091589521/379584101937898352000000000000)]
    bernstein := [(7954774143804130540935625434951/62191059261505265991680000000000), (106414909511493600727779600077001/777388240768815824896000000000000), (1362519324658474023100045959352439/9717353009610197811200000000000000), (3348683706567641559905159912123493/24293382524025494528000000000000000), (7877409083534635929990491512537599/60733456310063736320000000000000000)]
    reserve := (63954322681/500000000000) }

theorem quarter_043_020_valid : quarter_043_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_043_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_043_020]
  · intro i; fin_cases i <;> norm_num [quarter_043_020]
  · norm_num [quarter_043_020]
  · norm_num [quarter_043_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_043_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_043_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_043_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_043_020]

def quarter_043_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 3]
    lambda := ![0, (17258683/50000000), (32741317/100000000), (32741317/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (10224323/100000000), 0, 0], ![(85387/781250), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9698243/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (8972649/100000000), (106421/50000000), (1/100000000), (2127743/25000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-6012198133711551225963951509447/4643967027386400336000000000000), (1473667165321/83141406250), (-129304395522991623624323400389447/2321983513693200168000000000000), (1473667165321/83141406250), (-252596592912271696022682849269447/4643967027386400336000000000000)]
    bernstein := [(15224297668399449863668274562405199/106147817768832007680000000000000000), (226894147838926295983238707416861317/1486069448763648107520000000000000000), (1392755120415949223152664679861445219/8916416692581888645120000000000000000), (914994914011538352069613367177837437/5944277795054592430080000000000000000), (1733157144156703846372358702032048153/11888555590109184860160000000000000000)]
    reserve := (71712720941/500000000000) }

theorem quarter_043_021_valid : quarter_043_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_043_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_043_021]
  · intro i; fin_cases i <;> norm_num [quarter_043_021]
  · norm_num [quarter_043_021]
  · norm_num [quarter_043_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_043_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_043_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_043_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_043_021]

def quarter_043_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 3, 0, 0, 0, 2, 3]
    lambda := ![0, (34914361/100000000), (32542819/100000000), (32542819/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2585479/25000000), 0, 0], ![(12648221/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9639447/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (4537923/50000000), (53383/25000000), (1/100000000), (8459373/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1084906244690857865820446053/609220576031381600000000000), (441604554001781/21353200000000), (-17293333200913729839346317053/304610288015690800000000000), (441604554001781/21353200000000), (-33501760157136601812872188053/609220576031381600000000000)]
    bernstein := [(247939312296245145766976149054347/1559604674640336896000000000000000), (32858999968443855434139242902321/194950584330042112000000000000000), (3148873672477164757451072749921/18276617280941448000000000000000), (19931374212420788902173400529/117157803082958000000000000000), (1185949137472181599175775311/7322362692684875000000000000)]
    reserve := (15897574323/100000000000) }

theorem quarter_043_022_valid : quarter_043_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_043_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_043_022]
  · intro i; fin_cases i <;> norm_num [quarter_043_022]
  · norm_num [quarter_043_022]
  · norm_num [quarter_043_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_043_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_043_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_043_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_043_022]

def quarter_043_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 3]
    lambda := ![0, (8842737/25000000), (16157263/50000000), (16157263/50000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (10477161/100000000), 0, 0], ![(14383163/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (598239/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (4597267/50000000), (107157/50000000), (1/100000000), (8400029/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-77873722197546883566566035225213/33104805932563661208000000000000), (42395509212377/1785950000000), (-960658830050364019988310264505213/16552402966281830604000000000000), (42395509212377/1785950000000), (-1843443937903181156410054493785213/33104805932563661208000000000000)]
    bernstein := [(903374143861895220207428397899003/5172625926963072063750000000000000), (1388769605769629120653550195052389/7523819530128104820000000000000000), (187274115021840695041040351573625629/993144177976909836240000000000000000), (179623453229712439315891613865881993/963048899856397416960000000000000000), (15112786586261557969312628737703527907/84748303187362972692480000000000000000)]
    reserve := (43661292959/250000000000) }

theorem quarter_043_023_valid : quarter_043_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_043_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_043_023]
  · intro i; fin_cases i <;> norm_num [quarter_043_023]
  · norm_num [quarter_043_023]
  · norm_num [quarter_043_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_043_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_043_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_043_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_043_023]

def quarter_043_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 3, 0, 0, 0, 2, 3]
    lambda := ![0, (35888317/100000000), (16027921/50000000), (16027921/50000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (1063041/10000000), 0, 0], ![(8068369/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (11869/125000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (4664511/50000000), (26899/12500000), (1/100000000), (4166393/50000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-5794096913512966776615734609/1921912384721911312500000000), (289560184344973/10759600000000), (-457339445150699468253631303747/7687649538887645250000000000), (289560184344973/10759600000000), (-434163057496647601147168365311/7687649538887645250000000000)]
    bernstein := [(3749340215277918525581340551498329/19680382819552371840000000000000000), (197647295239060906226489699135723/984019140977618592000000000000000), (2816279390548937428441861161427/13730499641548166400000000000000), (499833162188817794146192893859/2460047852444046480000000000000), (10369372086785850954094202233/53190223836628032000000000000)]
    reserve := (19051154897/100000000000) }

theorem quarter_043_024_valid : quarter_043_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_043_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_043_024]
  · intro i; fin_cases i <;> norm_num [quarter_043_024]
  · norm_num [quarter_043_024]
  · norm_num [quarter_043_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_043_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_043_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_043_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_043_024]

def quarter_043_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 3]
    lambda := ![0, (36467829/100000000), (15883043/50000000), (15883043/50000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (5401033/50000000), 0, 0], ![(17911403/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2352343/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (592479/6250000), (108083/50000000), (1/100000000), (1651493/20000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-6386805025936356762464391877439/1692104078437299216000000000000), (653189981754087/21616600000000), (-51726992056443817457429440597439/846052039218649608000000000000), (653189981754087/21616600000000), (-97067179086951278152394489317439/1692104078437299216000000000000)]
    bernstein := [(3086699134941805056539940106901/14937194623446503424000000000000), (104657924588572098994631481267203/481309604533276221440000000000000), (28848945801298878061541055775459579/129953593223984579788800000000000000), (10597933306593419549233002796342139/48130960453327622144000000000000000), (917912298990240571547668151719954801/4331786440799485992960000000000000000)]
    reserve := (206645170847/1000000000000) }

theorem quarter_043_025_valid : quarter_043_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_043_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_043_025]
  · intro i; fin_cases i <;> norm_num [quarter_043_025]
  · norm_num [quarter_043_025]
  · norm_num [quarter_043_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_043_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_043_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_043_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_043_025]

def quarter_043_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 3, 0, 0, 0, 2, 3]
    lambda := ![0, (9277757/25000000), (15722243/50000000), (15722243/50000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (10992587/100000000), 0, 0], ![(1970971/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9314111/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (9646861/100000000), (5431/2500000), (1/100000000), (4086933/50000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-118597833625114211294884972747/25566926683591272000000000000), (18286189992047/543100000000), (-805280715386472568798710484747/12783463341795636000000000000), (18286189992047/543100000000), (-1491963597147830926302535996747/25566926683591272000000000000)]
    bernstein := [(14602763282212854945483211658868773/65451332309993656320000000000000000), (3835572340589528190314924384712829/16362833077498414080000000000000000), (2936473009933712603670033916030451/12272124808123810560000000000000000), (242994689763121589147601747331841/1022677067343650880000000000000000), (58610962754307702238180617048893/255669266835912720000000000000000)]
    reserve := (223108724709/1000000000000) }

theorem quarter_043_026_valid : quarter_043_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_043_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_043_026]
  · intro i; fin_cases i <;> norm_num [quarter_043_026]
  · norm_num [quarter_043_026]
  · norm_num [quarter_043_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_043_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_043_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_043_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_043_026]

def quarter_043_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 3, 0, 0, 0, 2, 3]
    lambda := ![0, (756393/2000000), (1243607/4000000), (1243607/4000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (11202487/100000000), 0, 0], ![(269179/1250000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4604581/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1228883/12500000), (43683/20000000), (1/100000000), (2020441/25000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-19490474642466906879295103037451/3470716529643367968000000000000), (67868370449/1820125000), (-112912087231596094705537223037451/1735358264821683984000000000000), (67868370449/1820125000), (-206333699820725282531779343037451/3470716529643367968000000000000)]
    bernstein := [(8328232418962804003142579292044669/34707165296433679680000000000000000), (34957625587007847844259144474932199/138828661185734718720000000000000000), (428189324206617640954910705134472387/1665943934228816624640000000000000000), (567502680411304651923314000642890459/2221258578971755499520000000000000000), (2194902829288820418259190353459301189/8885034315887021998080000000000000000)]
    reserve := (47991429711/200000000000) }

theorem quarter_043_027_valid : quarter_043_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_043_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_043_027]
  · intro i; fin_cases i <;> norm_num [quarter_043_027]
  · norm_num [quarter_043_027]
  · norm_num [quarter_043_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_043_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_043_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_043_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_043_027]

def quarter_043_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 3, 0, 0, 0, 2, 3]
    lambda := ![0, (9648909/25000000), (15351091/50000000), (15351091/50000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (571617/5000000), 0, 0], ![(11694007/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1818847/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (5016389/50000000), (13731/6250000), (1/100000000), (7980907/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-2952891921884274992970590175719/439780137854963690400000000000), (37611469796121/915400000000), (-14813061790412771300755979649719/219890068927481845200000000000), (37611469796121/915400000000), (-26673231658941267608541369123719/439780137854963690400000000000)]
    bernstein := [(289607216084096504557827853289266441/1125837152908707047424000000000000000), (4600269966678541350906261206909403/17058138680434955264000000000000000), (232438801164546206321781028624982083/844377864681530285568000000000000000), (1167965567649276431619821422774563/4264534670108738816000000000000000), (18668663250540358251881234838485881/70364822056794190464000000000000000)]
    reserve := (128618608533/500000000000) }

theorem quarter_043_028_valid : quarter_043_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_043_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_043_028]
  · intro i; fin_cases i <;> norm_num [quarter_043_028]
  · norm_num [quarter_043_028]
  · norm_num [quarter_043_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_043_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_043_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_043_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_043_028]

def quarter_043_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 3, 0, 0, 0, 2, 3]
    lambda := ![0, (19720573/50000000), (30279427/100000000), (30279427/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (11682787/100000000), 0, 0], ![(6318427/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8969011/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2050513/20000000), (44217/20000000), (1/100000000), (3935507/50000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-22680415425699938123471916482143/2854581696460229976000000000000), (124603000898671/2763562500000), (-33259901940493286369482729819381/475763616076704996000000000000), (124603000898671/2763562500000), (-10404646836309398829024968378479/167916570380013528000000000000)]
    bernstein := [(125595674631704441966965824124417057/456733071433636796160000000000000000), (52630386664879708104060371205200533/182693228573454718464000000000000000), (21490539329017527592283827192235081/73077291429381887385600000000000000), (8559427822631408010058551107844541/29230916571752754954240000000000000), (3322013469597050272138188119811953/11692366628701101981696000000000000)]
    reserve := (274987038353/1000000000000) }

theorem quarter_043_029_valid : quarter_043_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_043_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_043_029]
  · intro i; fin_cases i <;> norm_num [quarter_043_029]
  · norm_num [quarter_043_029]
  · norm_num [quarter_043_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_043_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_043_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_043_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_043_029]

def quarterTable043 : OwnerTable where
  mode := .quarter
  owners := ![0, 3, 0, 0, 0, 2, 3]
  rows := [quarter_043_000, quarter_043_001, quarter_043_002, quarter_043_003, quarter_043_004, quarter_043_005, quarter_043_006, quarter_043_007, quarter_043_008, quarter_043_009, quarter_043_010, quarter_043_011, quarter_043_012, quarter_043_013, quarter_043_014, quarter_043_015, quarter_043_016, quarter_043_017, quarter_043_018, quarter_043_019, quarter_043_020, quarter_043_021, quarter_043_022, quarter_043_023, quarter_043_024, quarter_043_025, quarter_043_026, quarter_043_027, quarter_043_028, quarter_043_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_043_000_valid
    · exact quarter_043_001_valid
    · exact quarter_043_002_valid
    · exact quarter_043_003_valid
    · exact quarter_043_004_valid
    · exact quarter_043_005_valid
    · exact quarter_043_006_valid
    · exact quarter_043_007_valid
    · exact quarter_043_008_valid
    · exact quarter_043_009_valid
    · exact quarter_043_010_valid
    · exact quarter_043_011_valid
    · exact quarter_043_012_valid
    · exact quarter_043_013_valid
    · exact quarter_043_014_valid
    · exact quarter_043_015_valid
    · exact quarter_043_016_valid
    · exact quarter_043_017_valid
    · exact quarter_043_018_valid
    · exact quarter_043_019_valid
    · exact quarter_043_020_valid
    · exact quarter_043_021_valid
    · exact quarter_043_022_valid
    · exact quarter_043_023_valid
    · exact quarter_043_024_valid
    · exact quarter_043_025_valid
    · exact quarter_043_026_valid
    · exact quarter_043_027_valid
    · exact quarter_043_028_valid
    · exact quarter_043_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
