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

def quarter_039_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 3, 0, 0, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(102465129/100000000), 0, (19192791/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(560543/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-9336687063886503438164777/457463486508250000000000), (-64079547/560543), (-40663458022347003438164777/228731743254125000000000), (-64079547/560543), (-71990228980807503438164777/457463486508250000000000)]
    bernstein := [(703685342559292178019903367/1873770440737792000000000000), (1875854259774222321528801499/4684426101844480000000000000), (14277826683957307031840585677/35133195763833600000000000000), (11531305198752544833786737987/29277663136528000000000000000), (26588901590914354362542792023/73194157841320000000000000000)]
    reserve := (36326535307/100000000000) }

theorem quarter_039_000_valid : quarter_039_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_039_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_039_000]
  · intro i; fin_cases i <;> norm_num [quarter_039_000]
  · norm_num [quarter_039_000]
  · norm_num [quarter_039_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_039_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_039_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_039_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_039_000]

def quarter_039_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(100371721/100000000), 0, (19887081/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(71153/12500000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-8208487042318949692827207/464548117886000000000000), (-60597559/569224), (-40668488900274449692827207/232274058943000000000000), (-60597559/569224), (-73128490758229949692827207/464548117886000000000000)]
    bernstein := [(25542887225243746976342241593/74327698861760000000000000000), (54783549554092372087240394787/148655397723520000000000000000), (111418677708706730449600452033/297310795447040000000000000000), (215717198152734591859305697947/594621590894080000000000000000), (396003581849212929304558675273/1189243181788160000000000000000)]
    reserve := (83246973351/250000000000) }

theorem quarter_039_001_valid : quarter_039_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_039_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_039_001]
  · intro i; fin_cases i <;> norm_num [quarter_039_001]
  · norm_num [quarter_039_001]
  · norm_num [quarter_039_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_039_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_039_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_039_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_039_001]

def quarter_039_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 3, 0, 0, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(19608541/20000000), 0, (41103203/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(577517/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-1426099006298046362438957/94263219891350000000000), (-56939502/577517), (-8135027509922696362438957/47131609945675000000000), (-56939502/577517), (-14843956013547346362438957/94263219891350000000000)]
    bernstein := [(74943659209813187891663083523/241313842921856000000000000000), (20236252696962981297167944413/60328460730464000000000000000), (15471642832850517916961408309/45246345547848000000000000000), (1246171032223673960933468593/3770528795654000000000000000), (284174818686034867862751883/942632198913500000000000000)]
    reserve := (301469458621/1000000000000) }

theorem quarter_039_002_valid : quarter_039_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_039_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_039_002]
  · intro i; fin_cases i <;> norm_num [quarter_039_002]
  · norm_num [quarter_039_002]
  · norm_num [quarter_039_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_039_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_039_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_039_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_039_002]

def quarter_039_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(47737769/50000000), 0, (84730841/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(585377/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-9773973405635598256572169/764369130194800000000000), (-106220235/1170754), (-65093570208929798256572169/382184565097400000000000), (-106220235/1170754), (-120413167012223998256572169/764369130194800000000000)]
    bernstein := [(2111975726260626713666060111/7643691301948000000000000000), (9208591601509896784563339707/30574765207792000000000000000), (37663862899051992598321534059/122299060831168000000000000000), (145308269583885004690215666383/489196243324672000000000000000), (525814725929969699756030396871/1956784973298688000000000000000)]
    reserve := (16794599723/62500000000) }

theorem quarter_039_003_valid : quarter_039_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_039_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_039_003]
  · intro i; fin_cases i <;> norm_num [quarter_039_003]
  · norm_num [quarter_039_003]
  · norm_num [quarter_039_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_039_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_039_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_039_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_039_003]

def quarter_039_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 3, 0, 0, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(231673/250000), 0, (21776787/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(592757/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-8238678976211038309129793/774005730506800000000000), (-49115626/592757), (-65109733826768638309129793/387002865253400000000000), (-49115626/592757), (-121980788677326238309129793/774005730506800000000000)]
    bernstein := [(477272706590133896248704771087/1981454670097408000000000000000), (52661339155095844167884088237/198145467009740800000000000000), (16217359561567344995261091973/59443640102922240000000000000), (519868938481048435359691749/1981454670097408000000000000), (46506272043574728661489823/198145467009740800000000000)]
    reserve := (9388309053/40000000000) }

theorem quarter_039_004_valid : quarter_039_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_039_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_039_004]
  · intro i; fin_cases i <;> norm_num [quarter_039_004]
  · norm_num [quarter_039_004]
  · norm_num [quarter_039_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_039_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_039_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_039_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_039_004]

def quarter_039_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(22406079/25000000), 0, (44660553/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(299807/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-17030661182269892909521343/1957398529634000000000000), (-44963763/599614), (-162821954872612892909521343/978699264817000000000000), (-44963763/599614), (-308613248562955892909521343/1957398529634000000000000)]
    bernstein := [(102349856194342949148331873/501094023586304000000000000), (1148422154004984670945181561/5010940235863040000000000000), (826745766726247431323963401/3496004815718400000000000000), (113485721831883046226991188473/501094023586304000000000000000), (999296720257540176098060282977/5010940235863040000000000000000)]
    reserve := (99711498563/500000000000) }

theorem quarter_039_005_valid : quarter_039_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_039_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_039_005]
  · intro i; fin_cases i <;> norm_num [quarter_039_005]
  · norm_num [quarter_039_005]
  · norm_num [quarter_039_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_039_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_039_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_039_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_039_005]

def quarter_039_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 3, 0, 0, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(345373/400000), 0, (22839737/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(37869/6250000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-1719924153567237495332851/247241475078000000000000), (-847162/12623), (-20359610527228987495332851/123620737539000000000000), (-847162/12623), (-12999765633630245831777617/82413825026000000000000)]
    bernstein := [(8102730097404880342365201953/48687552015360000000000000000), (15141896346211681502204791021/79117272024960000000000000000), (113495363872629455994497791/570557250180000000000000000), (39006384597562700060214611/206034562565000000000000000), (483828052294162560672937/2971652344687500000000000)]
    reserve := (40703621771/250000000000) }

theorem quarter_039_006_valid : quarter_039_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_039_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_039_006]
  · intro i; fin_cases i <;> norm_num [quarter_039_006]
  · norm_num [quarter_039_006]
  · norm_num [quarter_039_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_039_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_039_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_039_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_039_006]

def quarter_039_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(82830189/100000000), 0, (93207547/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(611587/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-2160864767049455192679741/399296712399400000000000), (-72452831/1223174), (-32587825353125155192679741/199648356199700000000000), (-72452831/1223174), (-63014785939200855192679741/399296712399400000000000)]
    bernstein := [(7944486300681222437123771/62390111312406250000000000), (152061772474782676498816969/998241780998500000000000000), (1917553159418961854195085037/11978901371982000000000000000), (19273738542380305840119167837/127774947967808000000000000000), (127591957454070811210055593059/1022199583742464000000000000000)]
    reserve := (15602622947/125000000000) }

theorem quarter_039_007_valid : quarter_039_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_039_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_039_007]
  · intro i; fin_cases i <;> norm_num [quarter_039_007]
  · norm_num [quarter_039_007]
  · norm_num [quarter_039_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_039_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_039_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_039_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_039_007]

def quarter_039_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 3, 0, 0, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(39545593/50000000), 0, (4742731/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(616623/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-16370826726713111514700481/4025846473026000000000000), (-31663876/616623), (-108672396249311037171566827/670974412171000000000000), (-31663876/616623), (-635663550769153111514700481/4025846473026000000000000)]
    bernstein := [(895909533610578656114937364319/10306166970946560000000000000000), (576888836997731191164562508251/5153083485473280000000000000000), (308891134286058906651146355479/2576541742736640000000000000000), (142956559643048917590240185491/1288270871368320000000000000000), (54986761533290832709388837839/644135435684160000000000000000)]
    reserve := (10670652181/125000000000) }

theorem quarter_039_008_valid : quarter_039_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_039_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_039_008]
  · intro i; fin_cases i <;> norm_num [quarter_039_008]
  · norm_num [quarter_039_008]
  · norm_num [quarter_039_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_039_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_039_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_039_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_039_008]

def quarter_039_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 3, 0, 0, 0, 0, 3]
    lambda := ![(2358989/20000000), (885457/5000000), (19755969/100000000), (19755969/100000000), (468361/5000000), (468361/5000000), (191399/1562500)]
    cone := fun i => (![![(826529/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5645313/100000000), 0, 0]] i.1) i.2
    mu := ![(19017/25000000), (5376413/100000000), (1494537/100000000), (1/100000000), (2762323/50000000), (1/100000000), (5645313/100000000)]
    alternative := .zero
    polynomial := [(-6118990447653514364356437878701836024119/22063785684959407139117723837250000000000), (-1349768271413/237712500000), (-241482307979550784852070065620116126249119/11031892842479703569558861918625000000000), (-1349768271413/237712500000), (-14449867439740850161811627071561527771943/668599566210891125427809813250000000000)]
    bernstein := [(318074417265180488312676777348873773791699561/3530205709593505142258835813960000000000000000), (134265252037646025652885401495379733322488627/1412082283837402056903534325584000000000000000), (23661884013152128637112328831176475399738709/242071248657840352612034455814400000000000000), (4433829999098547109084140916372678830729839/45186633082796865820913098418688000000000000), (347858251599022098999484175116911616929889/3614930646623749265673047873495040000000000)]
    reserve := (45050408309/500000000000) }

theorem quarter_039_009_valid : quarter_039_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_039_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_039_009]
  · intro i; fin_cases i <;> norm_num [quarter_039_009]
  · norm_num [quarter_039_009]
  · norm_num [quarter_039_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_039_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_039_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_039_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_039_009]

def quarter_039_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 3, 0, 0, 0, 0, 3]
    lambda := ![(2272399/20000000), (3640149/20000000), (200023/1000000), (200023/1000000), (1173711/12500000), (1173711/12500000), (5826641/50000000)]
    cone := fun i => (![![(2589219/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2747733/50000000), 0, 0]] i.1) i.2
    mu := ![(7279/10000000), (1084303/20000000), (1279697/100000000), (1/100000000), (5583361/100000000), (1/100000000), (2747733/50000000)]
    alternative := .zero
    polynomial := [(-43848275699592146485490783997990076783229/309905842970995863950736538314000000000000), (-16411281811929/3639500000000), (-3303252173080476556229957141897077021753229/154952921485497931975368269157000000000000), (-16411281811929/3639500000000), (-6562656070461360965974423499796163966723229/309905842970995863950736538314000000000000)]
    bernstein := [(4707317368589159838271895178539723894692699/50774973312367962349688674437365760000000000), (10318827309954511902967717959748029810969421/105781194400766588228518071744512000000000000), (595833885194881558343982025928664778409306677/5950192185043120587854141535628800000000000000), (83052721305249695287290455378928751936576517/826415581255988970535297435504000000000000000), (305710017244581470637019258267236316482620971/3099058429709958639507365383140000000000000000)]
    reserve := (46354700569/500000000000) }

theorem quarter_039_010_valid : quarter_039_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_039_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_039_010]
  · intro i; fin_cases i <;> norm_num [quarter_039_010]
  · norm_num [quarter_039_010]
  · norm_num [quarter_039_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_039_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_039_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_039_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_039_010]

def quarter_039_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 3]
    lambda := ![(2184579/20000000), (18723121/100000000), (20228561/100000000), (20228561/100000000), (940271/10000000), (940271/10000000), (11091443/100000000)]
    cone := fun i => (![![(385251/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (267607/5000000), 0, 0]] i.1) i.2
    mu := ![(69603/100000000), (1095437/20000000), (1049947/100000000), (1/100000000), (704569/12500000), (1/100000000), (267607/5000000)]
    alternative := .zero
    polynomial := [(-297534881283925150449998679177798466657/7546989508568736128111605105500000000000), (-7990439439297/2320100000000), (-79590740928076923020841872631089919961657/3773494754284368064055802552750000000000), (-7990439439297/2320100000000), (-158883946974869920891233746583002041456657/7546989508568736128111605105500000000000)]
    bernstein := [(7199418650881254980455904726471588997991943/75469895085687361281116051055000000000000000), (30222723340287759412047563483701598423327629/301879580342749445124464204220000000000000000), (371727417202700082203243012687686427180739161/3622554964112993341493570450640000000000000000), (497075646378391999464634339031776626475333961/4830073285483991121991427267520000000000000000), (1951740108108959625496946426606759764666169183/19320293141935964487965709070080000000000000000)]
    reserve := (95394576111/1000000000000) }

theorem quarter_039_011_valid : quarter_039_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_039_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_039_011]
  · intro i; fin_cases i <;> norm_num [quarter_039_011]
  · norm_num [quarter_039_011]
  · norm_num [quarter_039_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_039_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_039_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_039_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_039_011]

def quarter_039_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 3, 0, 0, 0, 0, 3]
    lambda := ![(5237377/50000000), (3856301/20000000), (2554461/12500000), (2554461/12500000), (9407727/100000000), (9407727/100000000), (10556909/100000000)]
    cone := fun i => (![![(1314479/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2606927/50000000), 0, 0]] i.1) i.2
    mu := ![(16619/25000000), (5544567/100000000), (402473/50000000), (1/100000000), (1136917/20000000), (1/100000000), (2606927/50000000)]
    alternative := .zero
    polynomial := [(46855877823786018271632801496918396133/1418290528258995873283702832400000000000), (-16440349838171/6647600000000), (-490997917270842751193029669779927306157/22875653681596707633608110200000000000), (-16440349838171/6647600000000), (-30488726748616036592239472327852411377867/1418290528258995873283702832400000000000)]
    bernstein := [(356367981214595199561547957473780132149223173/3630823752343029435606279250944000000000000000), (186591420948221612221329083549973124481878591/1815411876171514717803139625472000000000000000), (286361946332578553918484276946923605191375991/2723117814257272076704709438208000000000000000), (47790453866184539716398433109943436150787399/453852969042878679450784906368000000000000000), (23420740668856620109335507212279882911788533/226926484521439339725392453184000000000000000)]
    reserve := (24537681083/250000000000) }

theorem quarter_039_012_valid : quarter_039_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_039_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_039_012]
  · intro i; fin_cases i <;> norm_num [quarter_039_012]
  · norm_num [quarter_039_012]
  · norm_num [quarter_039_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_039_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_039_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_039_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_039_012]

def quarter_039_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 3]
    lambda := ![(5007053/50000000), (1242619/6250000), (20624701/100000000), (20624701/100000000), (9406139/100000000), (9406139/100000000), (1004231/10000000)]
    cone := fun i => (![![(188029/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5079049/100000000), 0, 0]] i.1) i.2
    mu := ![(31687/50000000), (225001/4000000), (544413/100000000), (1/100000000), (5727837/100000000), (1/100000000), (101581/2000000)]
    alternative := .zero
    polynomial := [(7484039312871285464726903285855643017/94099204500213932582906671125000000000), (-1259121699519/792175000000), (-1093503713416998384289487847053458458233/47049602250106966291453335562500000000), (-1259121699519/792175000000), (-731497155382289351347900865797590853161/31366401500071310860968890375000000000)]
    bernstein := [(1519967178420377496338190898536538698874117/15055872720034229213265067380000000000000000), (3178155087242299025431625437572254097125917/30111745440068458426530134760000000000000000), (2779822417495926701455204794256282132999993/25810067520058678651311544080000000000000000), (12940836887468940934129075203280777751216317/120446981760273833706120539040000000000000000), (25235933165541014195888049071024541715214917/240893963520547667412241078080000000000000000)]
    reserve := (50477551407/500000000000) }

theorem quarter_039_013_valid : quarter_039_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_039_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_039_013]
  · intro i; fin_cases i <;> norm_num [quarter_039_013]
  · norm_num [quarter_039_013]
  · norm_num [quarter_039_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_039_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_039_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_039_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_039_013]

def quarter_039_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 3, 0, 0, 0, 0, 3]
    lambda := ![(37253/390625), (5132827/25000000), (20796781/100000000), (20796781/100000000), (4699653/50000000), (4699653/50000000), (9539749/100000000)]
    cone := fun i => (![![(29807/12500000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4946019/100000000), 0, 0]] i.1) i.2
    mu := ![(30129/50000000), (5720201/100000000), (134733/50000000), (1/100000000), (1153343/20000000), (1/100000000), (4946019/100000000)]
    alternative := .zero
    polynomial := [(759196588119917255059816780481302069447/7358880429112087094281668820500000000000), (-593645187809/753225000000), (-37698818357034764190405320136355074861851/1226480071518681182380278136750000000000), (-593645187809/753225000000), (-226952106730328502397491737598611751240553/7358880429112087094281668820500000000000)]
    bernstein := [(1952827665404400186216487692034471548128109847/18838733898526942961361072180480000000000000000), (106304059756879701542636393588937931493731/981184057214944945904222509400000000000000), (431003992507642186568646761787855860217783/3924736228859779783616890037600000000000000), (66287118147703878437293032663281405381/613240035759340591190139068375000000000), (759196588119917255059816780481302069447/7358880429112087094281668820500000000000)]
    reserve := (51583701857/500000000000) }

theorem quarter_039_014_valid : quarter_039_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_039_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_039_014]
  · intro i; fin_cases i <;> norm_num [quarter_039_014]
  · norm_num [quarter_039_014]
  · norm_num [quarter_039_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_039_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_039_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_039_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_039_014]

def quarter_039_015 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 3]
    lambda := ![(4523601/50000000), (21099717/100000000), (33749/160000), (33749/160000), (1172609/12500000), (1172609/12500000), (4452543/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(527411/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (238773/5000000), 0, 0]] i.1) i.2
    mu := ![(59459/50000000), (2900459/50000000), (133277/100000000), (1/100000000), (5833137/100000000), (1/100000000), (238773/5000000)]
    alternative := .zero
    polynomial := [(2255270636182683420778431373424076540899/21342027423977925047533187958000000000000), (13501909136331/13327700000000), (-426382930884904840927812865022530524869101/10671013711988962523766593979000000000000), (13501909136331/13327700000000), (-855021132405992365276404161418485126279101/21342027423977925047533187958000000000000)]
    bernstein := [(2255270636182683420778431373424076540899/21342027423977925047533187958000000000000), (597600461388680421588629818962282180131/5335506855994481261883296989500000000000), (11696175732763542928339101590693537795846099/102441731635094040228159302198400000000000000), (957703755800636086337118837999666863737231/8536810969591170019013275183200000000000000), (5792820852373220958257333827140174433303637699/54635590205383488121684961172480000000000000000)]
    reserve := (4226909827/40000000000) }

theorem quarter_039_015_valid : quarter_039_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_039_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_039_015]
  · intro i; fin_cases i <;> norm_num [quarter_039_015]
  · norm_num [quarter_039_015]
  · norm_num [quarter_039_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_039_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_039_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_039_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_039_015]

def quarter_039_016 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 3, 0, 0, 0, 0, 3]
    lambda := ![(8567789/100000000), (5391457/25000000), (21505259/100000000), (21505259/100000000), (4671437/50000000), (4671437/50000000), (2042529/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(807583/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1143399/25000000), 0, 0]] i.1) i.2
    mu := ![(46767/20000000), (1465887/25000000), (68047/50000000), (1/100000000), (23143/390625), (1/100000000), (1143399/25000000)]
    alternative := .zero
    polynomial := [(8825907562766520139311291712358563621/125402408072155408677930048000000000000), (661717851451/243025000000), (-2315594191360844356692626171537506012379/62701204036077704338965024000000000000), (661717851451/243025000000), (-662859184326350747646366233541052941197/17914629724593629811132864000000000000)]
    bernstein := [(37046273080231718710904763488956654000358821/321030164664717846215500922880000000000000000), (6468355692777400434078297383337773612594007/53505027444119641035916820480000000000000000), (29505900495324550738256885688003679252984063/240772623498538384661625692160000000000000000), (229989565966799329530821900444076540060801/1910893837289987179854172160000000000000000), (134909587864810113199992943904062964074613/1180257958326168552262871040000000000000000)]
    reserve := (14288146387/125000000000) }

theorem quarter_039_016_valid : quarter_039_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_039_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_039_016]
  · intro i; fin_cases i <;> norm_num [quarter_039_016]
  · norm_num [quarter_039_016]
  · norm_num [quarter_039_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_039_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_039_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_039_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_039_016]

def quarter_039_017 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 3]
    lambda := ![(4047979/50000000), (11031029/50000000), (21890369/100000000), (21890369/100000000), (2322849/25000000), (2322849/25000000), (3739227/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(2747027/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4379521/100000000), 0, 0]] i.1) i.2
    mu := ![(332921/100000000), (742267/12500000), (69461/50000000), (1/100000000), (6008889/100000000), (1/100000000), (2189761/50000000)]
    alternative := .zero
    polynomial := [(-682102150803228462066987181495654949351/64530529486092174277291654338000000000000), (31341456287371/6946100000000), (-1181025307915835686287747295882223589719351/32265264743046087138645827169000000000000), (31341456287371/6946100000000), (-2361368513680868144113427604582951524489351/64530529486092174277291654338000000000000)]
    bernstein := [(1278847928083467700113492896998090160067469849/10324884717774747884366664694080000000000000000), (2669627514414918056508586671523836349450409947/20649769435549495768733329388160000000000000000), (16218595841760270541202234180836883650869472723/123898616613296974612399976328960000000000000000), (10631539405777292327633349399716964048805195523/82599077742197983074933317552640000000000000000), (20267700755564388029763695460229380853294893769/165198155484395966149866635105280000000000000000)]
    reserve := (12268720977/100000000000) }

theorem quarter_039_017_valid : quarter_039_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_039_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_039_017]
  · intro i; fin_cases i <;> norm_num [quarter_039_017]
  · norm_num [quarter_039_017]
  · norm_num [quarter_039_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_039_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_039_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_039_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_039_017]

def quarter_039_018 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 3, 0, 0, 0, 0, 3]
    lambda := ![(7629933/100000000), (22591741/100000000), (22248433/100000000), (22248433/100000000), (184557/2000000), (184557/2000000), (6825759/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(784703/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (524059/12500000), 0, 0]] i.1) i.2
    mu := ![(103977/25000000), (6025253/100000000), (141771/100000000), (1/100000000), (3043053/50000000), (1/100000000), (524059/12500000)]
    alternative := .zero
    polynomial := [(-152313426371112781034813459371646627/1084774873155158494985334750000000000), (90574424047993/14177100000000), (-40122281273070070953957933497076441379/1084774873155158494985334750000000000), (90574424047993/14177100000000), (-312265373802335610725961875294568709/8474803696524675742072927734375000)]
    bernstein := [(11474977612869348461633810305817435017109/86781989852412679598826780000000000000000), (118667523586187256428180331439819325141/861359700768364065497040000000000000000), (36311786931622017329505570134780910717923/260345969557238038796480340000000000000000), (924156645747297962221086167477386253/6729372662252844261695625000000000000), (356090871307921561271291500328757680587/2711937182887896237463336875000000000000)]
    reserve := (131304985069/1000000000000) }

theorem quarter_039_018_valid : quarter_039_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_039_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_039_018]
  · intro i; fin_cases i <;> norm_num [quarter_039_018]
  · norm_num [quarter_039_018]
  · norm_num [quarter_039_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_039_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_039_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_039_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_039_018]

def quarter_039_019 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 3, 0, 0, 0, 0, 3]
    lambda := ![(716791/10000000), (361847/1562500), (11289671/50000000), (11289671/50000000), (1144191/12500000), (1144191/12500000), (3104071/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(2572737/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4011769/100000000), 0, 0]] i.1) i.2
    mu := ![(241689/50000000), (1225101/20000000), (36163/25000000), (1/100000000), (769543/12500000), (1/100000000), (4011769/100000000)]
    alternative := .zero
    polynomial := [(-47443584593495819021485169828303643181/146919527383665093885375537640000000000), (1511949968297/180815000000), (-8311618692541430370290015230942888516343/220379291075497640828063306460000000000), (1511949968297/180815000000), (-16480906631302373283515574952400866103143/440758582150995281656126612920000000000)]
    bernstein := [(620305611779018253084617267837659338158257/4407585821509952816561266129200000000000000), (516522386155293129771666222053986537823117/3526068657207962253249012903360000000000000), (1255307832667566098194115548613855584706959/8462564777299109407797630968064000000000000), (66012324387431373380601606928945776473461/451336788122619168415873651630080000000000), (10125498527806469516512694943109303932673/72213886099619066946539784260812800000000)]
    reserve := (140215394499/1000000000000) }

theorem quarter_039_019_valid : quarter_039_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_039_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_039_019]
  · intro i; fin_cases i <;> norm_num [quarter_039_019]
  · norm_num [quarter_039_019]
  · norm_num [quarter_039_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_039_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_039_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_039_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_039_019]

def quarter_039_020 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 3, 0, 0, 0, 0, 3]
    lambda := ![0, (27152517/100000000), (26144863/100000000), (26144863/100000000), (5139439/50000000), (5139439/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (1608559/20000000), 0, 0], ![(732839/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (859/32000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3529093/50000000), (42153/25000000), (1/100000000), (3549253/50000000), (1/100000000), (859/32000)]
    alternative := .zero
    polynomial := [(-11968884148465608750907315942646171/18141855562390413835320000000000000), (6632807801921/562040000000), (-393877709322117776695978700306696171/9070927781195206917660000000000000), (6632807801921/562040000000), (-775786534495769944641050084670746171/18141855562390413835320000000000000)]
    bernstein := [(444563730642749187053163246534137101/2972361615342045402778828800000000000), (5827559100083240791414905989792983651/37154520191775567534735360000000000000), (222436093456270458588264529331965809367/1393294507191583782552576000000000000000), (183370826384954401604153423593534017943/1161078755992986485460480000000000000000), (440176559557960292402240942522289768949/2902696889982466213651200000000000000000)]
    reserve := (149565829523/1000000000000) }

theorem quarter_039_020_valid : quarter_039_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_039_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_039_020]
  · intro i; fin_cases i <;> norm_num [quarter_039_020]
  · norm_num [quarter_039_020]
  · norm_num [quarter_039_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_039_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_039_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_039_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_039_020]

def quarter_039_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 3]
    lambda := ![0, (27638311/100000000), (5243243/20000000), (5243243/20000000), (9964629/100000000), (9964629/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2046673/25000000), 0, 0], ![(8751361/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (650577/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (7184467/100000000), (6817/4000000), (1/100000000), (7086689/100000000), (1/100000000), (650577/25000000)]
    alternative := .zero
    polynomial := [(-149197832755212289691105001426534931/150535409694329028181378000000000000), (14227813940663/1002500000000), (-3349248539319842894971164876516416931/75267704847164514090689000000000000), (14227813940663/1002500000000), (-6549299245884473500251224751606298931/150535409694329028181378000000000000)]
    bernstein := [(3911714617723147752327811313504524347389/24085665551092644509020480000000000000000), (8188817838107347949360460357094262262441/48171331102185289018040960000000000000000), (16666996176781981227796259722082055547029/96342662204370578036081920000000000000000), (1942406722990930358064771619355017531953/11334430847573009180715520000000000000000), (3741623160036345005793423887559143985757/22668861695146018361431040000000000000000)]
    reserve := (40602102207/250000000000) }

theorem quarter_039_021_valid : quarter_039_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_039_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_039_021]
  · intro i; fin_cases i <;> norm_num [quarter_039_021]
  · norm_num [quarter_039_021]
  · norm_num [quarter_039_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_039_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_039_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_039_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_039_021]

def quarter_039_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 3, 0, 0, 0, 0, 3]
    lambda := ![0, (7042757/25000000), (6564381/25000000), (6564381/25000000), (4828481/50000000), (4828481/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (8344487/100000000), 0, 0], ![(10205353/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2521959/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (114421/1562500), (17229/10000000), (1/100000000), (7069237/100000000), (1/100000000), (2521959/100000000)]
    alternative := .zero
    polynomial := [(-4176066171567778551238924072300817237/2999128572668356487487744000000000000), (71873821278221/4307250000000), (-68557624456686465845509369193584913237/1499564286334178243743872000000000000), (71873821278221/4307250000000), (-132939182741805153139779814314869009237/2999128572668356487487744000000000000)]
    bernstein := [(449098003270324706130405189134104467940121/2559256382010330869322874880000000000000000), (58672782727191301356126074211729225444903/319907047751291358665359360000000000000000), (16792123314567444578048809677493304895109/89973857180050694624632320000000000000000), (462632520676601837909225118723630234411/2499273810556963739573120000000000000000), (83765958852063035089801970282517918947/468613839479430701169960000000000000000)]
    reserve := (87739940091/500000000000) }

theorem quarter_039_022_valid : quarter_039_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_039_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_039_022]
  · intro i; fin_cases i <;> norm_num [quarter_039_022]
  · norm_num [quarter_039_022]
  · norm_num [quarter_039_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_039_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_039_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_039_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_039_022]

def quarter_039_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 3]
    lambda := ![0, (14376173/50000000), (26267841/100000000), (26267841/100000000), (4677993/50000000), (4677993/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (4258339/50000000), 0, 0], ![(1169179/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1221679/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1494811/20000000), (43553/25000000), (1/100000000), (1761451/25000000), (1/100000000), (1221679/50000000)]
    alternative := .zero
    polynomial := [(-2111437502601256375680995594262421/1129822840859748931174250000000000), (16808319571967/871060000000), (-13301033632489091720687278687992773/282455710214937232793562500000000), (16808319571967/871060000000), (-51092697027355110507068119157708671/1129822840859748931174250000000000)]
    bernstein := [(4167244087126120477453416961761747/22066852360541971311997070312500000), (1113722960395961669093738574808722411/5649114204298744655871250000000000000), (877430192922085339554844563273754637/4373507771069995862610000000000000000), (9002520720337188515726880338362163827/45192913634389957246970000000000000000), (557646812097592912645153404627525626369/2892346472600957263806080000000000000000)]
    reserve := (188846330189/1000000000000) }

theorem quarter_039_023_valid : quarter_039_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_039_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_039_023]
  · intro i; fin_cases i <;> norm_num [quarter_039_023]
  · norm_num [quarter_039_023]
  · norm_num [quarter_039_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_039_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_039_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_039_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_039_023]

def quarter_039_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 3, 0, 0, 0, 0, 3]
    lambda := ![0, (29384049/100000000), (13123079/50000000), (13123079/50000000), (9061817/100000000), (9061817/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (8703793/100000000), 0, 0], ![(6606087/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1183267/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (954783/12500000), (176191/100000000), (1/100000000), (3508017/50000000), (1/100000000), (473307/20000000)]
    alternative := .zero
    polynomial := [(-2409475476006741540488196045645642557/993117155095368866403936000000000000), (194113584106263/8809550000000), (-24144700775510029205831275066817802557/496558577547684433201968000000000000), (194113584106263/8809550000000), (-45879926075013316871174354087989962557/993117155095368866403936000000000000)]
    bernstein := [(515007188540992121631011941927568240569123/2542379917044144297994076160000000000000000), (53717684629651122274081053949269729384427/254237991704414429799407616000000000000000), (16400758753422607986450126234157567147657/76271397511324328939822284800000000000000), (543358433556511060161422944722747973739/2542379917044144297994076160000000000000), (52693630026050039937102557374861141027/254237991704414429799407616000000000000)]
    reserve := (25321116697/125000000000) }

theorem quarter_039_024_valid : quarter_039_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_039_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_039_024]
  · intro i; fin_cases i <;> norm_num [quarter_039_024]
  · norm_num [quarter_039_024]
  · norm_num [quarter_039_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_039_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_039_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_039_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_039_024]

def quarter_039_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 3]
    lambda := ![0, (30068033/100000000), (13095703/50000000), (13095703/50000000), (8774577/100000000), (8774577/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (1781279/20000000), 0, 0], ![(14768103/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (7161/312500), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (7816063/100000000), (178231/100000000), (1/100000000), (1744891/25000000), (1/100000000), (2291521/100000000)]
    alternative := .zero
    polynomial := [(-68424235846996335557360886771754168019/22280422937930644315750732000000000000), (444047808351399/17823100000000), (-560660971569508818655208787559286448019/11140211468965322157875366000000000000), (444047808351399/17823100000000), (-1052897707292021301753056688346818728019/22280422937930644315750732000000000000)]
    bernstein := [(1236032995940810521941481486859974962509/5703788272110244944832187392000000000000), (12883724901643286091877925247286517048767/57037882721102449448321873920000000000000), (393414916605567701802077876324151232500959/1711136481633073483449656217600000000000000), (1304566892122243340743061172262342310440471/5703788272110244944832187392000000000000000), (12673209113233940396102004689521417668677021/57037882721102449448321873920000000000000000)]
    reserve := (216703870651/1000000000000) }

theorem quarter_039_025_valid : quarter_039_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_039_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_039_025]
  · intro i; fin_cases i <;> norm_num [quarter_039_025]
  · norm_num [quarter_039_025]
  · norm_num [quarter_039_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_039_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_039_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_039_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_039_025]

def quarter_039_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 3, 0, 0, 0, 0, 3]
    lambda := ![0, (1232253/4000000), (26102459/100000000), (26102459/100000000), (8494379/100000000), (8494379/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (9125083/100000000), 0, 0], ![(654451/4000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (443669/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (8007979/100000000), (180333/100000000), (1/100000000), (3468011/50000000), (1/100000000), (1109173/50000000)]
    alternative := .zero
    polynomial := [(-84675452296940722030186774774525837057/22219684093204284380341284000000000000), (29868489189/1068640000), (-580073159097390875407396868685375337057/11109842046602142190170642000000000000), (29868489189/1068640000), (-1075470865897841028784606962596224837057/22219684093204284380341284000000000000)]
    bernstein := [(13157023327929315511047832402560239786258063/56882391278602968013673687040000000000000000), (3426825758913662941727991527780389211482999/14220597819650742003418421760000000000000000), (2616507611252953664588122731943498316354681/10665448364738056502563816320000000000000000), (217087753491234622954055383620682602920771/888787363728171375213651360000000000000000), (52802088583925546581990227420571060925783/222196840932042843803412840000000000000000)]
    reserve := (46260443811/200000000000) }

theorem quarter_039_026_valid : quarter_039_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_039_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_039_026]
  · intro i; fin_cases i <;> norm_num [quarter_039_026]
  · norm_num [quarter_039_026]
  · norm_num [quarter_039_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_039_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_039_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_039_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_039_026]

def quarter_039_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 3, 0, 0, 0, 0, 3]
    lambda := ![0, (31601097/100000000), (12989063/50000000), (12989063/50000000), (328853/4000000), (328853/4000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (9360501/100000000), 0, 0], ![(17993507/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (536759/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (8214577/100000000), (91251/50000000), (1/100000000), (6885023/100000000), (1/100000000), (536759/25000000)]
    alternative := .zero
    polynomial := [(-51566053001737589024376888553120711801/11080709243565573515211756000000000000), (63179395564131/2027800000000), (-300784343828634786869279466058030291801/5540354621782786757605878000000000000), (63179395564131/2027800000000), (-550002634655531984714182043562939871801/11080709243565573515211756000000000000)]
    bernstein := [(27303917439014261505922441449866874532319/110807092435655735152117560000000000000000), (113743187619235838942353037678637385900349/443228369742622940608470240000000000000000), (198550806538804108721670660071421810891191/759820062415925041043091840000000000000000), (1846413379195097361009488033840911098739609/7091653915881967049735523840000000000000000), (7195136565931505714239099137977779910550839/28366615663527868198942095360000000000000000)]
    reserve := (24640947469/100000000000) }

theorem quarter_039_027_valid : quarter_039_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_039_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_039_027]
  · intro i; fin_cases i <;> norm_num [quarter_039_027]
  · norm_num [quarter_039_027]
  · norm_num [quarter_039_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_039_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_039_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_039_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_039_027]

def quarter_039_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 3, 0, 0, 0, 0, 3]
    lambda := ![0, (32454687/100000000), (25817159/100000000), (25817159/100000000), (7955497/100000000), (7955497/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (9613341/100000000), 0, 0], ![(4916687/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1038807/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (527279/6250000), (9237/5000000), (1/100000000), (106659/1562500), (1/100000000), (1038807/50000000)]
    alternative := .zero
    polynomial := [(-93173425690335524545312937833063/16612281367291358784000000000000), (53189845887323/1539500000000), (-469898231631983458912512163897063/8306140683645679392000000000000), (53189845887323/1539500000000), (-846623037573631393279711389961063/16612281367291358784000000000000)]
    bernstein := [(11144966957699935585774071315931209257/42527440300265878487040000000000000000), (644683219982000528299987220892275747/2362635572236993249280000000000000000), (8864374305585048555808222957055768291/31895580225199408865280000000000000000), (163670885524730980456734444899028587/590658893059248312320000000000000000), (718349927775541421594091584462298137/2657965018766617405440000000000000000)]
    reserve := (262065313101/1000000000000) }

theorem quarter_039_028_valid : quarter_039_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_039_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_039_028]
  · intro i; fin_cases i <;> norm_num [quarter_039_028]
  · norm_num [quarter_039_028]
  · norm_num [quarter_039_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_039_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_039_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_039_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_039_028]

def quarter_039_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 3, 0, 0, 0, 0, 3]
    lambda := ![0, (19720573/50000000), (30279427/100000000), (30279427/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (11682787/100000000), 0, 0], ![(6318427/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8969011/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2050513/20000000), (44217/20000000), (1/100000000), (3935507/50000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-22680415425699938123471916482143/2854581696460229976000000000000), (124603000898671/2763562500000), (-33259901940493286369482729819381/475763616076704996000000000000), (124603000898671/2763562500000), (-10404646836309398829024968378479/167916570380013528000000000000)]
    bernstein := [(125595674631704441966965824124417057/456733071433636796160000000000000000), (52630386664879708104060371205200533/182693228573454718464000000000000000), (21490539329017527592283827192235081/73077291429381887385600000000000000), (8559427822631408010058551107844541/29230916571752754954240000000000000), (3322013469597050272138188119811953/11692366628701101981696000000000000)]
    reserve := (274987038353/1000000000000) }

theorem quarter_039_029_valid : quarter_039_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_039_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_039_029]
  · intro i; fin_cases i <;> norm_num [quarter_039_029]
  · norm_num [quarter_039_029]
  · norm_num [quarter_039_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_039_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_039_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_039_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_039_029]

def quarterTable039 : OwnerTable where
  mode := .quarter
  owners := ![0, 3, 0, 0, 0, 0, 3]
  rows := [quarter_039_000, quarter_039_001, quarter_039_002, quarter_039_003, quarter_039_004, quarter_039_005, quarter_039_006, quarter_039_007, quarter_039_008, quarter_039_009, quarter_039_010, quarter_039_011, quarter_039_012, quarter_039_013, quarter_039_014, quarter_039_015, quarter_039_016, quarter_039_017, quarter_039_018, quarter_039_019, quarter_039_020, quarter_039_021, quarter_039_022, quarter_039_023, quarter_039_024, quarter_039_025, quarter_039_026, quarter_039_027, quarter_039_028, quarter_039_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_039_000_valid
    · exact quarter_039_001_valid
    · exact quarter_039_002_valid
    · exact quarter_039_003_valid
    · exact quarter_039_004_valid
    · exact quarter_039_005_valid
    · exact quarter_039_006_valid
    · exact quarter_039_007_valid
    · exact quarter_039_008_valid
    · exact quarter_039_009_valid
    · exact quarter_039_010_valid
    · exact quarter_039_011_valid
    · exact quarter_039_012_valid
    · exact quarter_039_013_valid
    · exact quarter_039_014_valid
    · exact quarter_039_015_valid
    · exact quarter_039_016_valid
    · exact quarter_039_017_valid
    · exact quarter_039_018_valid
    · exact quarter_039_019_valid
    · exact quarter_039_020_valid
    · exact quarter_039_021_valid
    · exact quarter_039_022_valid
    · exact quarter_039_023_valid
    · exact quarter_039_024_valid
    · exact quarter_039_025_valid
    · exact quarter_039_026_valid
    · exact quarter_039_027_valid
    · exact quarter_039_028_valid
    · exact quarter_039_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
