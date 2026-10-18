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

def quarter_015_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 1, 0, 0, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(102465129/100000000), 0, (19192791/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(560543/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-9336687063886503438164777/457463486508250000000000), (-64079547/560543), (-40663458022347003438164777/228731743254125000000000), (-64079547/560543), (-71990228980807503438164777/457463486508250000000000)]
    bernstein := [(703685342559292178019903367/1873770440737792000000000000), (1875854259774222321528801499/4684426101844480000000000000), (14277826683957307031840585677/35133195763833600000000000000), (11531305198752544833786737987/29277663136528000000000000000), (26588901590914354362542792023/73194157841320000000000000000)]
    reserve := (36326535307/100000000000) }

theorem quarter_015_000_valid : quarter_015_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_015_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_015_000]
  · intro i; fin_cases i <;> norm_num [quarter_015_000]
  · norm_num [quarter_015_000]
  · norm_num [quarter_015_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_015_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_015_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_015_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_015_000]

def quarter_015_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(100371721/100000000), 0, (19887081/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(71153/12500000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-8208487042318949692827207/464548117886000000000000), (-60597559/569224), (-40668488900274449692827207/232274058943000000000000), (-60597559/569224), (-73128490758229949692827207/464548117886000000000000)]
    bernstein := [(25542887225243746976342241593/74327698861760000000000000000), (54783549554092372087240394787/148655397723520000000000000000), (111418677708706730449600452033/297310795447040000000000000000), (215717198152734591859305697947/594621590894080000000000000000), (396003581849212929304558675273/1189243181788160000000000000000)]
    reserve := (83246973351/250000000000) }

theorem quarter_015_001_valid : quarter_015_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_015_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_015_001]
  · intro i; fin_cases i <;> norm_num [quarter_015_001]
  · norm_num [quarter_015_001]
  · norm_num [quarter_015_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_015_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_015_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_015_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_015_001]

def quarter_015_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 1, 0, 0, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(19608541/20000000), 0, (41103203/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(577517/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-1426099006298046362438957/94263219891350000000000), (-56939502/577517), (-8135027509922696362438957/47131609945675000000000), (-56939502/577517), (-14843956013547346362438957/94263219891350000000000)]
    bernstein := [(74943659209813187891663083523/241313842921856000000000000000), (20236252696962981297167944413/60328460730464000000000000000), (15471642832850517916961408309/45246345547848000000000000000), (1246171032223673960933468593/3770528795654000000000000000), (284174818686034867862751883/942632198913500000000000000)]
    reserve := (301469458621/1000000000000) }

theorem quarter_015_002_valid : quarter_015_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_015_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_015_002]
  · intro i; fin_cases i <;> norm_num [quarter_015_002]
  · norm_num [quarter_015_002]
  · norm_num [quarter_015_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_015_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_015_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_015_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_015_002]

def quarter_015_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(47737769/50000000), 0, (84730841/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(585377/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-9773973405635598256572169/764369130194800000000000), (-106220235/1170754), (-65093570208929798256572169/382184565097400000000000), (-106220235/1170754), (-120413167012223998256572169/764369130194800000000000)]
    bernstein := [(2111975726260626713666060111/7643691301948000000000000000), (9208591601509896784563339707/30574765207792000000000000000), (37663862899051992598321534059/122299060831168000000000000000), (145308269583885004690215666383/489196243324672000000000000000), (525814725929969699756030396871/1956784973298688000000000000000)]
    reserve := (16794599723/62500000000) }

theorem quarter_015_003_valid : quarter_015_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_015_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_015_003]
  · intro i; fin_cases i <;> norm_num [quarter_015_003]
  · norm_num [quarter_015_003]
  · norm_num [quarter_015_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_015_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_015_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_015_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_015_003]

def quarter_015_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 1, 0, 0, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(231673/250000), 0, (21776787/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(592757/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-8238678976211038309129793/774005730506800000000000), (-49115626/592757), (-65109733826768638309129793/387002865253400000000000), (-49115626/592757), (-121980788677326238309129793/774005730506800000000000)]
    bernstein := [(477272706590133896248704771087/1981454670097408000000000000000), (52661339155095844167884088237/198145467009740800000000000000), (16217359561567344995261091973/59443640102922240000000000000), (519868938481048435359691749/1981454670097408000000000000), (46506272043574728661489823/198145467009740800000000000)]
    reserve := (9388309053/40000000000) }

theorem quarter_015_004_valid : quarter_015_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_015_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_015_004]
  · intro i; fin_cases i <;> norm_num [quarter_015_004]
  · norm_num [quarter_015_004]
  · norm_num [quarter_015_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_015_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_015_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_015_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_015_004]

def quarter_015_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(22406079/25000000), 0, (44660553/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(299807/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-17030661182269892909521343/1957398529634000000000000), (-44963763/599614), (-162821954872612892909521343/978699264817000000000000), (-44963763/599614), (-308613248562955892909521343/1957398529634000000000000)]
    bernstein := [(102349856194342949148331873/501094023586304000000000000), (1148422154004984670945181561/5010940235863040000000000000), (826745766726247431323963401/3496004815718400000000000000), (113485721831883046226991188473/501094023586304000000000000000), (999296720257540176098060282977/5010940235863040000000000000000)]
    reserve := (99711498563/500000000000) }

theorem quarter_015_005_valid : quarter_015_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_015_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_015_005]
  · intro i; fin_cases i <;> norm_num [quarter_015_005]
  · norm_num [quarter_015_005]
  · norm_num [quarter_015_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_015_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_015_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_015_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_015_005]

def quarter_015_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 1, 0, 0, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(345373/400000), 0, (22839737/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(37869/6250000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-1719924153567237495332851/247241475078000000000000), (-847162/12623), (-20359610527228987495332851/123620737539000000000000), (-847162/12623), (-12999765633630245831777617/82413825026000000000000)]
    bernstein := [(8102730097404880342365201953/48687552015360000000000000000), (15141896346211681502204791021/79117272024960000000000000000), (113495363872629455994497791/570557250180000000000000000), (39006384597562700060214611/206034562565000000000000000), (483828052294162560672937/2971652344687500000000000)]
    reserve := (40703621771/250000000000) }

theorem quarter_015_006_valid : quarter_015_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_015_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_015_006]
  · intro i; fin_cases i <;> norm_num [quarter_015_006]
  · norm_num [quarter_015_006]
  · norm_num [quarter_015_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_015_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_015_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_015_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_015_006]

def quarter_015_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(82830189/100000000), 0, (93207547/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(611587/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-2160864767049455192679741/399296712399400000000000), (-72452831/1223174), (-32587825353125155192679741/199648356199700000000000), (-72452831/1223174), (-63014785939200855192679741/399296712399400000000000)]
    bernstein := [(7944486300681222437123771/62390111312406250000000000), (152061772474782676498816969/998241780998500000000000000), (1917553159418961854195085037/11978901371982000000000000000), (19273738542380305840119167837/127774947967808000000000000000), (127591957454070811210055593059/1022199583742464000000000000000)]
    reserve := (15602622947/125000000000) }

theorem quarter_015_007_valid : quarter_015_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_015_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_015_007]
  · intro i; fin_cases i <;> norm_num [quarter_015_007]
  · norm_num [quarter_015_007]
  · norm_num [quarter_015_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_015_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_015_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_015_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_015_007]

def quarter_015_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 1, 0, 0, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(39545593/50000000), 0, (4742731/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(616623/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-16370826726713111514700481/4025846473026000000000000), (-31663876/616623), (-108672396249311037171566827/670974412171000000000000), (-31663876/616623), (-635663550769153111514700481/4025846473026000000000000)]
    bernstein := [(895909533610578656114937364319/10306166970946560000000000000000), (576888836997731191164562508251/5153083485473280000000000000000), (308891134286058906651146355479/2576541742736640000000000000000), (142956559643048917590240185491/1288270871368320000000000000000), (54986761533290832709388837839/644135435684160000000000000000)]
    reserve := (10670652181/125000000000) }

theorem quarter_015_008_valid : quarter_015_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_015_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_015_008]
  · intro i; fin_cases i <;> norm_num [quarter_015_008]
  · norm_num [quarter_015_008]
  · norm_num [quarter_015_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_015_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_015_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_015_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_015_008]

def quarter_015_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 1, 0, 0, 0, 0, 3]
    lambda := ![(4654939/20000000), (20477571/100000000), (11008711/100000000), (11008711/100000000), (1257323/25000000), (1257323/25000000), (24171729/100000000)]
    cone := fun i => (![![(6523883/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (7625977/100000000), 0, 0]] i.1) i.2
    mu := ![(75051/50000000), (178269/10000000), (2937297/50000000), (1/100000000), (3058217/100000000), (1/100000000), (3812989/50000000)]
    alternative := .zero
    polynomial := [(-63652819885073109989161940255258044170371/101836041659773990332040579302000000000000), (-54613660209397/5003400000000), (-162170494410103894013487575263615940861567/3916770833068230397386176127000000000000), (-54613660209397/5003400000000), (-4152780034777628134361515016598756418230371/101836041659773990332040579302000000000000)]
    bernstein := [(1577990431303273771573543477527619856732708749/16293766665563838453126492688320000000000000000), (52688608824547674703662333523903841864772811/501346666632733490865430544256000000000000000), (852234381960298262043652266817639971842792767/7821007999470642457500716490393600000000000000), (22632685033226436113430982709883841498229851/208560213319217132200019106410496000000000000), (133202980668280780646060587126905539629177/1283447466579797736615502193295360000000000)]
    reserve := (96846264199/1000000000000) }

theorem quarter_015_009_valid : quarter_015_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_015_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_015_009]
  · intro i; fin_cases i <;> norm_num [quarter_015_009]
  · norm_num [quarter_015_009]
  · norm_num [quarter_015_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_015_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_015_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_015_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_015_009]

def quarter_015_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 1, 0, 0, 0, 0, 3]
    lambda := ![(4608569/20000000), (5187819/25000000), (5587349/50000000), (5587349/50000000), (1022289/20000000), (1022289/20000000), (23633593/100000000)]
    cone := fun i => (![![(5251099/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1501379/20000000), 0, 0]] i.1) i.2
    mu := ![(73811/50000000), (1487963/100000000), (595537/10000000), (1/100000000), (97031/3125000), (1/100000000), (469181/6250000)]
    alternative := .zero
    polynomial := [(-1792992507827831922100318999198269103727/4764231723780198183365101201600000000000), (-130229026300051/14762200000000), (-97325596936326968683448275390786858563727/2382115861890099091682550600800000000000), (-130229026300051/14762200000000), (-192858201364826105444796231782375448023727/4764231723780198183365101201600000000000)]
    bernstein := [(74418986461871982430420517869651993020537/780571725624147670362538180870144000000000), (504608843141720846574240439467182112905869/4878573285150922939765863630438400000000000), (9807915129653307974248952716929730735662551/91473249096579805120609943070720000000000000), (131243991155320820284092263714027172593723/1229479154523922111836155148800000000000000), (4861438965115537826700226005295078057240873/47642317237801981833651012016000000000000000)]
    reserve := (95339075217/1000000000000) }

theorem quarter_015_010_valid : quarter_015_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_015_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_015_010]
  · intro i; fin_cases i <;> norm_num [quarter_015_010]
  · norm_num [quarter_015_010]
  · norm_num [quarter_015_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_015_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_015_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_015_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_015_010]

def quarter_015_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 3]
    lambda := ![(22777799/100000000), (10498069/50000000), (2836407/25000000), (2836407/25000000), (2601383/50000000), (2601383/50000000), (925171/4000000)]
    cone := fun i => (![![(4016869/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (7399039/100000000), 0, 0]] i.1) i.2
    mu := ![(18143/12500000), (1188261/100000000), (6030329/100000000), (1/100000000), (788467/25000000), (1/100000000), (11561/156250)]
    alternative := .zero
    polynomial := [(-388333845143313111104905270624129372869/2106775923343609197571332496000000000000), (-99002194647719/14514400000000), (-385768191475435997979095100372708924545821/9480491655046241389070996232000000000000), (-99002194647719/14514400000000), (-768041378344582177958246053309800684735821/18960983310092482778141992464000000000000)]
    bernstein := [(17753773766350587160171272437161761279289979/189609833100924827781419924640000000000000000), (77056919826993261952842025713282060002927837/758439332403699311125679698560000000000000000), (958243974446314151139293242624752896092659533/9101271988844391733508156382720000000000000000), (423643326023349541844831253281770170488848811/4045009772819729659336958392320000000000000000), (539101090776100592982252331796262464562910411/5393346363759639545782611189760000000000000000)]
    reserve := (93633191253/1000000000000) }

theorem quarter_015_011_valid : quarter_015_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_015_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_015_011]
  · intro i; fin_cases i <;> norm_num [quarter_015_011]
  · norm_num [quarter_015_011]
  · norm_num [quarter_015_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_015_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_015_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_015_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_015_011]

def quarter_015_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 1, 0, 0, 0, 0, 3]
    lambda := ![(899197/4000000), (21210273/100000000), (576119/5000000), (576119/5000000), (2652201/50000000), (2652201/50000000), (22656239/100000000)]
    cone := fun i => (![![(282101/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3651023/50000000), 0, 0]] i.1) i.2
    mu := ![(142663/100000000), (885467/100000000), (6099179/100000000), (1/100000000), (3205173/100000000), (1/100000000), (7302047/100000000)]
    alternative := .zero
    polynomial := [(-512146902631429243623674741511590143901/11312612068694945924795403628500000000000), (-17491329783847/3566575000000), (-232901734621637036575326338877602801893901/5656306034347472962397701814250000000000), (-17491329783847/3566575000000), (-465291322340642643907029003013694013643901/11312612068694945924795403628500000000000)]
    bernstein := [(2655672205681060184224259988323882476756735219/28960286895859061567476233288960000000000000000), (1441754071545725633416627173273969220318822673/14480143447929530783738116644480000000000000000), (2239703238082963250784975359385217738208959873/21720215171894296175607174966720000000000000000), (370600225672057785427854050483536135099246297/3620035861982382695934529161120000000000000000), (176217274512784210492273569328517000580275299/1810017930991191347967264580560000000000000000)]
    reserve := (733603839/8000000000) }

theorem quarter_015_012_valid : quarter_015_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_015_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_015_012]
  · intro i; fin_cases i <;> norm_num [quarter_015_012]
  · norm_num [quarter_015_012]
  · norm_num [quarter_015_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_015_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_015_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_015_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_015_012]

def quarter_015_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 3]
    lambda := ![(22149987/100000000), (21391667/100000000), (2341117/20000000), (2341117/20000000), (5417403/100000000), (5417403/100000000), (22212371/100000000)]
    cone := fun i => (![![(415897/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (7215639/100000000), 0, 0]] i.1) i.2
    mu := ![(70087/50000000), (116359/20000000), (6161581/100000000), (1/100000000), (3259171/100000000), (1/100000000), (180391/2500000)]
    alternative := .zero
    polynomial := [(2603949725658047899519985770660386295807/59085596219726147993810234306000000000000), (-83885439272/27377734375), (-1274935772214411836410596693098097722305193/29542798109863073996905117153000000000000), (-83885439272/27377734375), (-2552475494154481720720713371966855830906193/59085596219726147993810234306000000000000)]
    bernstein := [(846058821074416540209631816214676753737259407/9453695395156183679009637488960000000000000000), (1839852052982225133776754344246256227805102207/18907390790312367358019274977920000000000000000), (11413318199488946811509751434837128720604117821/113444344741874204148115649867520000000000000000), (7518529615286766843024445662506344478575190607/75629563161249469432077099911680000000000000000), (14177463409128945407898863064427130437904796207/151259126322498938864154199823360000000000000000)]
    reserve := (223737593/2500000000) }

theorem quarter_015_013_valid : quarter_015_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_015_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_015_013]
  · intro i; fin_cases i <;> norm_num [quarter_015_013]
  · norm_num [quarter_015_013]
  · norm_num [quarter_015_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_015_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_015_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_015_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_015_013]

def quarter_015_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 1, 0, 0, 0, 0, 3]
    lambda := ![(10894587/50000000), (2153819/10000000), (11895611/100000000), (11895611/100000000), (1385679/25000000), (1385679/25000000), (1362249/6250000)]
    cone := fun i => (![![(272407/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (892453/12500000), 0, 0]] i.1) i.2
    mu := ![(5507/4000000), (280863/100000000), (1554289/25000000), (1/100000000), (414507/12500000), (1/100000000), (892453/12500000)]
    alternative := .zero
    polynomial := [(4658418845259614983023348483228368119/53898249315944920613549526000000000000), (-4451324460869/3441875000000), (-1375262595991835739153341567700931249481/26949124657972460306774763000000000000), (-4451324460869/3441875000000), (-2755183610828931093289706483885090867081/53898249315944920613549526000000000000)]
    bernstein := [(11985915165520902512134111267659809112521719/137979518248818996770686786560000000000000000), (8169816739954271215506697465854406481339/86237198905511872981679241600000000000000), (25167494906014770381711937154657870153719/258711596716535618945037724800000000000000), (5094079995755495629101807441859892539/53898249315944920613549526000000000000), (4658418845259614983023348483228368119/53898249315944920613549526000000000000)]
    reserve := (21607468259/250000000000) }

theorem quarter_015_014_valid : quarter_015_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_015_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_015_014]
  · intro i; fin_cases i <;> norm_num [quarter_015_014]
  · norm_num [quarter_015_014]
  · norm_num [quarter_015_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_015_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_015_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_015_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_015_014]

def quarter_015_015 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 3]
    lambda := ![(1339691/6250000), (5360439/25000000), (589793/5000000), (589793/5000000), (5480507/100000000), (5480507/100000000), (4514091/20000000)]
    cone := fun i => (![![0, 0, (564173/50000000), 0, 0], ![(13399/2500000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3662817/50000000), 0, 0]] i.1) i.2
    mu := ![(142567/100000000), (135437/100000000), (6183649/100000000), (1/100000000), (821643/25000000), (1/100000000), (1465127/20000000)]
    alternative := .zero
    polynomial := [(3637096680279993939906820845644824418231/47911342804231916733792635477000000000000), (846918831346285653/386176935580000000), (-1665023247709349117023446129121010893911769/23955671402115958366896317738500000000000), (846918831346285653/386176935580000000), (-3333683592098978227986799079087666612241769/47911342804231916733792635477000000000000)]
    bernstein := [(3637096680279993939906820845644824418231/47911342804231916733792635477000000000000), (8587613930170413117024519086051983173337/95822685608463833467585270954000000000000), (22097459551764662933141505424833351130597031/229974445460313200322204650289600000000000000), (14614395036176933937504356820075383501852537/153316296973542133548136433526400000000000000), (10708475687482898908737214021430819258219457431/122653037578833706838509146821120000000000000000)]
    reserve := (3795653041/50000000000) }

theorem quarter_015_015_valid : quarter_015_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_015_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_015_015]
  · intro i; fin_cases i <;> norm_num [quarter_015_015]
  · norm_num [quarter_015_015]
  · norm_num [quarter_015_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_015_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_015_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_015_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_015_015]

def quarter_015_016 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 1, 0, 0, 0, 0, 3]
    lambda := ![(5501209/25000000), (5516703/25000000), (5981047/50000000), (5981047/50000000), (5498221/100000000), (5498221/100000000), (10503861/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1652687/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3461073/50000000), 0, 0]] i.1) i.2
    mu := ![(3739/625000), (27851/20000000), (3171199/50000000), (1/100000000), (166329/5000000), (1/100000000), (3461073/50000000)]
    alternative := .zero
    polynomial := [(5910444677037667032185910818140723867/126738111389931421730315658000000000000), (2645024623629/870343750000), (-2693407817321047630408168910720601701633/63369055694965710865157829000000000000), (2645024623629/870343750000), (-5392726079319132927848523732259344127133/126738111389931421730315658000000000000)]
    bernstein := [(31172368595512307517721651515369371199127267/324449565158224439629608084480000000000000000), (1835094924477982208821721369739061329505963/18024975842123579979422671360000000000000000), (3584665186961953983604475416985434159418143/34762453409809761388886580480000000000000000), (450643428146160076492726709088312792550363/4506243960530894994855667840000000000000000), (1874570629815485708285569215522534781766467/20278097822389027476850505280000000000000000)]
    reserve := (23110779993/250000000000) }

theorem quarter_015_016_valid : quarter_015_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_015_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_015_016]
  · intro i; fin_cases i <;> norm_num [quarter_015_016]
  · norm_num [quarter_015_016]
  · norm_num [quarter_015_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_015_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_015_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_015_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_015_016]

def quarter_015_017 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 3]
    lambda := ![(5553551/25000000), (22388433/100000000), (2992291/25000000), (2992291/25000000), (5445773/100000000), (5445773/100000000), (20567491/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(557533/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (169837/2500000), 0, 0]] i.1) i.2
    mu := ![(454371/50000000), (140977/100000000), (3207401/50000000), (1/100000000), (3322693/100000000), (1/100000000), (6793481/100000000)]
    alternative := .zero
    polynomial := [(-92819402929370541975165551621664180469601/2318807603150998812922322252455500000000000), (68210537436359/14097700000000), (-15607879971989598340866353229527685368854867/386467933858499802153720375409250000000000), (68210537436359/14097700000000), (-93554460429008219503222953825544448032659601/2318807603150998812922322252455500000000000)]
    bernstein := [(12525220991040028210960578555692844812611066533/123669738834719936689190520130960000000000000000), (98300519970830985979212640598259413592724999/924057824418828916731186949920000000000000000), (53071368454333908561772915641784429693770713997/494678955338879746756762080523840000000000000000), (384344542768136406554797466063439801553176991/3696231297675315666924747799680000000000000000), (572516813170589512636606014968850143451415303519/5936147464066556961081144966286080000000000000000)]
    reserve := (96445854257/1000000000000) }

theorem quarter_015_017_valid : quarter_015_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_015_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_015_017]
  · intro i; fin_cases i <;> norm_num [quarter_015_017]
  · norm_num [quarter_015_017]
  · norm_num [quarter_015_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_015_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_015_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_015_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_015_017]

def quarter_015_018 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 1, 0, 0, 0, 0, 3]
    lambda := ![(44747/200000), (22718737/100000000), (11997923/100000000), (11997923/100000000), (338119/6250000), (338119/6250000), (20092109/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(3945571/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1331993/20000000), 0, 0]] i.1) i.2
    mu := ![(60601/5000000), (17821/12500000), (1298383/20000000), (1/100000000), (3325573/100000000), (1/100000000), (1331993/20000000)]
    alternative := .zero
    polynomial := [(-811837976236511289622104507122047310287/4658481475370415363282096995250000000000), (95367373455651/14256800000000), (-23123816188210182955075287591806051753353/582310184421301920410262124406250000000), (95367373455651/14256800000000), (-184178691529444952350980196227326366716537/4658481475370415363282096995250000000000)]
    bernstein := [(1259627505237128879205019162437199455516187403/11925712576948263330002168307840000000000000000), (101359956195924261053018741433300708901982033/917362505919097179230936023680000000000000000), (497479742268519740330754174949376027478762427/4472142216355598748750813115440000000000000000), (6183587660498673485423190187179811089312487/57335156619943573701933501480000000000000000), (2335888858394499502303968453987883725913969/23292407376852076816410484976250000000000000)]
    reserve := (100285420077/1000000000000) }

theorem quarter_015_018_valid : quarter_015_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_015_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_015_018]
  · intro i; fin_cases i <;> norm_num [quarter_015_018]
  · norm_num [quarter_015_018]
  · norm_num [quarter_015_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_015_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_015_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_015_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_015_018]

def quarter_015_019 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 1, 0, 0, 0, 0, 3]
    lambda := ![(4496551/20000000), (4611829/20000000), (6023869/50000000), (6023869/50000000), (5389539/100000000), (5389539/100000000), (19583547/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(640433/12500000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6521833/100000000), 0, 0]] i.1) i.2
    mu := ![(752761/50000000), (72017/50000000), (6573917/100000000), (1/100000000), (3334947/100000000), (1/100000000), (3260917/50000000)]
    alternative := .zero
    polynomial := [(-1638670279975266644081991669061202902223/4575743000338452029791519893000000000000), (30946023123869/3600850000000), (-90678774188431405683015498886204179352223/2287871500169226014895759946500000000000), (30946023123869/3600850000000), (-179718878096887544721949006103347155802223/4575743000338452029791519893000000000000)]
    bernstein := [(5015406606318451656621509673550940371723177/45757430003384520297915198930000000000000000), (1396003173828026082120761224287649380067879/12201981334235872079444053048000000000000000), (10112178260701561196565838353602081927175799/87854265606498278971997181945600000000000000), (174400083034438869077610162060392775361727/1561853610782191626168838790144000000000000), (78002448632058672561889846704611024400313/749689733175451980561042619269120000000000)]
    reserve := (52023153833/500000000000) }

theorem quarter_015_019_valid : quarter_015_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_015_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_015_019]
  · intro i; fin_cases i <;> norm_num [quarter_015_019]
  · norm_num [quarter_015_019]
  · norm_num [quarter_015_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_015_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_015_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_015_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_015_019]

def quarter_015_020 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 1, 0, 0, 0, 0, 3]
    lambda := ![(901693/4000000), (23411133/100000000), (6058923/50000000), (6058923/50000000), (5383561/100000000), (5383561/100000000), (1190233/6250000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(31593/500000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (199353/3125000), 0, 0]] i.1) i.2
    mu := ![(111699/6250000), (145379/100000000), (3330499/50000000), (1/100000000), (209407/6250000), (1/100000000), (199353/3125000)]
    alternative := .zero
    polynomial := [(-245661425029425092628084010389527483/413704689151021046129208000000000000), (19182837654953/1817237500000), (-1559532068848349139059911496169058694287/39095093124771488859210156000000000000), (19182837654953/1817237500000), (-3072634128366136935613115114374496694287/78190186249542977718420312000000000000)]
    bernstein := [(111775435986025037096658975565358526269/985436931932701651491229532160000000000), (18935318135895435314217909697088633253847/160133501439064018367324798976000000000000), (714236445419013960347481317473960543117499/6005006303964900688774679961600000000000000), (192612313218290281808863886351521658682857/1668057306656916857992966656000000000000000), (149831624108777902587871409114955754641817/1390047755547430714994138880000000000000000)]
    reserve := (53894416041/500000000000) }

theorem quarter_015_020_valid : quarter_015_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_015_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_015_020]
  · intro i; fin_cases i <;> norm_num [quarter_015_020]
  · norm_num [quarter_015_020]
  · norm_num [quarter_015_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_015_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_015_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_015_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_015_020]

def quarter_015_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 3]
    lambda := ![(11276429/50000000), (5944059/25000000), (9537/78125), (9537/78125), (2695407/50000000), (2695407/50000000), (9237279/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(3764239/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6232549/100000000), 0, 0]] i.1) i.2
    mu := ![(2055207/100000000), (14661/10000000), (3376681/50000000), (1/100000000), (1685967/50000000), (1/100000000), (6232549/100000000)]
    alternative := .zero
    polynomial := [(-681704973673162265792242034293430409049/771366439006094989931687698500000000000), (640333262311/50906250000), (-15569862765354063175902738346465202913049/385683219503047494965843849250000000000), (640333262311/50906250000), (-30458020557034964086013234658636975417049/771366439006094989931687698500000000000)]
    bernstein := [(14463045786185935708113940705597743600146231/123418630240975198389070031760000000000000000), (30135301678300397271058779824879860154053339/246837260481950396778140063520000000000000000), (181890008261121899718196203997704795178525373/1481023562891702380668840381120000000000000000), (117817902455840409082092846439917788385169379/987349041927801587112560254080000000000000000), (220313616663828781291145029409636936005102151/1974698083855603174225120508160000000000000000)]
    reserve := (11156825363/100000000000) }

theorem quarter_015_021_valid : quarter_015_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_015_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_015_021]
  · intro i; fin_cases i <;> norm_num [quarter_015_021]
  · norm_num [quarter_015_021]
  · norm_num [quarter_015_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_015_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_015_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_015_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_015_021]

def quarter_015_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 1, 0, 0, 0, 0, 3]
    lambda := ![0, (20274879/50000000), (10328153/50000000), (10328153/50000000), (1813763/20000000), (1813763/20000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(2072437/12500000), 0, (7559087/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1184181/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (247997/100000000), (11498927/100000000), (1/100000000), (5700309/100000000), (1/100000000), (1184181/50000000)]
    alternative := .zero
    polynomial := [(-18300030283928642362135756017054215303/8555348655354425692303756000000000000), (1191329526848463/49599400000000), (-282655867793628288074297280530644415303/4277674327677212846151878000000000000), (1191329526848463/49599400000000), (-547011705303327933786458805044234615303/8555348655354425692303756000000000000)]
    bernstein := [(2397497090885194973240611446779093979867097/21901692557707329772297615360000000000000000), (329257169137997375799219115119325144603071/2737711569713416221537201920000000000000000), (31896480603070711340890052982111050503171/256660459660632770769112680000000000000000), (2596728413934643588332917107762226769627/21388371638386064230759390000000000000000), (149132496614350198710726020800017663793/1336773227399129014422461875000000000000)]
    reserve := (4378651713/40000000000) }

theorem quarter_015_022_valid : quarter_015_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_015_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_015_022]
  · intro i; fin_cases i <;> norm_num [quarter_015_022]
  · norm_num [quarter_015_022]
  · norm_num [quarter_015_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_015_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_015_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_015_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_015_022]

def quarter_015_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 3]
    lambda := ![0, (4246681/10000000), (10140869/50000000), (10140869/50000000), (8484857/100000000), (8484857/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1920847/10000000), 0, (38797231/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1107929/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (64327/25000000), (2972871/25000000), (1/100000000), (2777589/50000000), (1/100000000), (2215859/100000000)]
    alternative := .zero
    polynomial := [(-6067909386242780165747891504948600761/2092458922157237035306608000000000000), (1466685428021089/51461600000000), (-73060076344373800697945701381900400761/1046229461078618517653304000000000000), (1466685428021089/51461600000000), (-140052243302504821230143511258852200761/2092458922157237035306608000000000000)]
    bernstein := [(41804636726016129082146104235009721391/326946706587068286766657500000000000000), (66293838501969060180133282950647162033/475558845944826598933320000000000000000), (9025236501194948074499065147439411651813/62773767664717111059198240000000000000000), (8575707576602955237826603755971173969421/60871532280937804663464960000000000000000), (699595945534794041344416447939574876595879/5356694840722526810384916480000000000000000)]
    reserve := (63931882297/500000000000) }

theorem quarter_015_023_valid : quarter_015_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_015_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_015_023]
  · intro i; fin_cases i <;> norm_num [quarter_015_023]
  · norm_num [quarter_015_023]
  · norm_num [quarter_015_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_015_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_015_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_015_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_015_023]

def quarter_015_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 1, 0, 0, 0, 0, 3]
    lambda := ![0, (2219193/5000000), (3976701/20000000), (3976701/20000000), (1584913/20000000), (1584913/20000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(21938861/100000000), 0, (7928831/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (413907/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (66533/25000000), (6144439/50000000), (1/100000000), (5408489/100000000), (1/100000000), (64673/3125000)]
    alternative := .zero
    polynomial := [(-3734653128682012345098628247512133663/980531383876462837040496000000000000), (177150660783309/5322640000000), (-36149101879254991909706711263474133663/490265691938231418520248000000000000), (177150660783309/5322640000000), (-68563550629827971474314794279436133663/980531383876462837040496000000000000)]
    bernstein := [(368699295287448189542748041096190920307457/2510160342723744862823669760000000000000000), (39962353776567191934651473699517867211993/251016034272374486282366976000000000000000), (12347664737982423591184002726226204814563/75304810281712345884710092800000000000000), (404304428997384331392989810454604586201/2510160342723744862823669760000000000000), (37741106061766226720699528866342171393/251016034272374486282366976000000000000)]
    reserve := (9180172901/62500000000) }

theorem quarter_015_024_valid : quarter_015_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_015_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_015_024]
  · intro i; fin_cases i <;> norm_num [quarter_015_024]
  · norm_num [quarter_015_024]
  · norm_num [quarter_015_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_015_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_015_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_015_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_015_024]

def quarter_015_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 3]
    lambda := ![0, (11571329/25000000), (4866439/25000000), (4866439/25000000), (3695793/50000000), (3695793/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(12374607/50000000), 0, (40317819/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (965173/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (6859/2500000), (12687571/100000000), (1/100000000), (1315319/25000000), (1/100000000), (965173/50000000)]
    alternative := .zero
    polynomial := [(-17236063788343988450493085074064892021/3535293906794014096622176000000000000), (5261095205496669/137180000000000), (-137466659464389702862593181109383724021/1767646953397007048311088000000000000), (5261095205496669/137180000000000), (-257697255140435417274693277144702556021/3535293906794014096622176000000000000)]
    bernstein := [(150701213391511875298408069798763172331/905035240139267608735277056000000000000), (1625958829152699527004131015838124698153/9050352401392676087352770560000000000000), (50188115994375262723761838068657020342281/271510572041780282620583116800000000000000), (164672612097567274882622780587948386652689/905035240139267608735277056000000000000000), (1545846770468177370167712281874253764397339/9050352401392676087352770560000000000000000)]
    reserve := (166514193821/1000000000000) }

theorem quarter_015_025_valid : quarter_015_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_015_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_015_025]
  · intro i; fin_cases i <;> norm_num [quarter_015_025]
  · norm_num [quarter_015_025]
  · norm_num [quarter_015_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_015_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_015_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_015_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_015_025]

def quarter_015_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 1, 0, 0, 0, 0, 3]
    lambda := ![0, (48154213/100000000), (4758413/25000000), (4758413/25000000), (6889241/100000000), (6889241/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1725927/6250000), 0, (4080147/10000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (449789/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (70471/25000000), (13083623/100000000), (1/100000000), (5114767/100000000), (1/100000000), (1799157/100000000)]
    alternative := .zero
    polynomial := [(-29613328302449442923218712384206394551/4848365191134541549136244000000000000), (2463064736465121/56376800000000), (-198581538141577414077934676447531444551/2424182595567270774568122000000000000), (2463064736465121/56376800000000), (-367549747980705385232650640510856494551/4848365191134541549136244000000000000)]
    bernstein := [(2317779854270524232758239090360460970771609/12411814889304426365788784640000000000000000), (622899681451003321755592055388431453019157/3102953722326106591447196160000000000000000), (480306511549420572373149194958894721102583/2327215291744579943585397120000000000000000), (39468172387342765837939526594142398613953/193934607645381661965449760000000000000000), (9305825237405616986397444197772478089569/48483651911345415491362440000000000000000)]
    reserve := (3734796039/20000000000) }

theorem quarter_015_026_valid : quarter_015_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_015_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_015_026]
  · intro i; fin_cases i <;> norm_num [quarter_015_026]
  · norm_num [quarter_015_026]
  · norm_num [quarter_015_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_015_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_015_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_015_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_015_026]

def quarter_015_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 1, 0, 0, 0, 0, 3]
    lambda := ![0, (49972563/100000000), (18593287/100000000), (18593287/100000000), (6420431/100000000), (6420431/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(30508161/100000000), 0, (5135081/12500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (419181/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1443/500000), (13472767/100000000), (1/100000000), (2485183/50000000), (1/100000000), (67069/4000000)]
    alternative := .zero
    polynomial := [(-973741231830344435783742604997269/129617406277152180867480000000000), (2369876223456003/48100000000000), (-1116758837024087331611616171873257/12961740627715218086748000000000), (2369876223456003/48100000000000), (-10193847138410528880332419113735301/129617406277152180867480000000000)]
    bernstein := [(20692137308340469467707793804667259/99705697136270908359600000000000000), (288311010461522986987079169834557957/1296174062771521808674800000000000000), (2031389994025224223298329472095030841/8888050716147578116627200000000000000), (1872444807463590063386775361727143957/8295514001737739575518720000000000000), (70916658435828229880415455836597099451/331820560069509583020748800000000000000)]
    reserve := (51883036533/250000000000) }

theorem quarter_015_027_valid : quarter_015_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_015_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_015_027]
  · intro i; fin_cases i <;> norm_num [quarter_015_027]
  · norm_num [quarter_015_027]
  · norm_num [quarter_015_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_015_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_015_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_015_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_015_027]

def quarter_015_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 1, 0, 0, 0, 0, 3]
    lambda := ![0, (51721811/100000000), (1134471/6250000), (1134471/6250000), (5987559/100000000), (5987559/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(33399347/100000000), 0, (41143833/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (781839/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (294413/100000000), (2770103/20000000), (1/100000000), (4829621/100000000), (1/100000000), (781839/50000000)]
    alternative := .zero
    polynomial := [(-118525175960814156336139860160706661/13035012879146902505495200000000000), (32421460706906777/588826000000000), (-589614169768756268997364367839982661/6517506439573451252747600000000000), (32421460706906777/588826000000000), (-1060703163576698381658588875519258661/13035012879146902505495200000000000)]
    bernstein := [(7636800844610481304117185899284653306379/33369632970616070414067712000000000000000), (4082445919596305306876151740840185953681/16684816485308035207033856000000000000000), (2096467793636994787376354087348953219859/8342408242654017603516928000000000000000), (1036640867857035449866374640183062533001/4171204121327008801758464000000000000000), (492436658320852746950116239252777427739/2085602060663504400879232000000000000000)]
    reserve := (114427402473/500000000000) }

theorem quarter_015_028_valid : quarter_015_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_015_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_015_028]
  · intro i; fin_cases i <;> norm_num [quarter_015_028]
  · norm_num [quarter_015_028]
  · norm_num [quarter_015_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_015_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_015_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_015_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_015_028]

def quarter_015_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 1, 0, 0, 0, 0, 3]
    lambda := ![0, (427067/800000), (17715841/100000000), (17715841/100000000), (699059/12500000), (699059/12500000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(36256977/100000000), 0, (40983039/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1460499/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (299237/100000000), (14212291/100000000), (1/100000000), (938837/20000000), (1/100000000), (2921/200000)]
    alternative := .zero
    polynomial := [(-22007801783707077386179835552179797/2028305146259690448532000000000000), (292180664412567/4787792000000), (-96155588394266762057444036844679797/1014152573129845224266000000000000), (292180664412567/4787792000000), (-170303375004826446728708238137179797/2028305146259690448532000000000000)]
    bernstein := [(81347341477994959012070053721060745003/324528823401550471765120000000000000000), (34716501501065349783182103001778327607/129811529360620188706048000000000000000), (14257585355966719306340399235604544899/51924611744248075482419200000000000000), (5646825760973995445840848682105092239/20769844697699230192967680000000000000), (2152299232866393050729433685202861787/8307937879079692077187072000000000000)]
    reserve := (31332864607/125000000000) }

theorem quarter_015_029_valid : quarter_015_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_015_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_015_029]
  · intro i; fin_cases i <;> norm_num [quarter_015_029]
  · norm_num [quarter_015_029]
  · norm_num [quarter_015_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_015_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_015_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_015_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_015_029]

def quarterTable015 : OwnerTable where
  mode := .quarter
  owners := ![0, 1, 0, 0, 0, 0, 3]
  rows := [quarter_015_000, quarter_015_001, quarter_015_002, quarter_015_003, quarter_015_004, quarter_015_005, quarter_015_006, quarter_015_007, quarter_015_008, quarter_015_009, quarter_015_010, quarter_015_011, quarter_015_012, quarter_015_013, quarter_015_014, quarter_015_015, quarter_015_016, quarter_015_017, quarter_015_018, quarter_015_019, quarter_015_020, quarter_015_021, quarter_015_022, quarter_015_023, quarter_015_024, quarter_015_025, quarter_015_026, quarter_015_027, quarter_015_028, quarter_015_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_015_000_valid
    · exact quarter_015_001_valid
    · exact quarter_015_002_valid
    · exact quarter_015_003_valid
    · exact quarter_015_004_valid
    · exact quarter_015_005_valid
    · exact quarter_015_006_valid
    · exact quarter_015_007_valid
    · exact quarter_015_008_valid
    · exact quarter_015_009_valid
    · exact quarter_015_010_valid
    · exact quarter_015_011_valid
    · exact quarter_015_012_valid
    · exact quarter_015_013_valid
    · exact quarter_015_014_valid
    · exact quarter_015_015_valid
    · exact quarter_015_016_valid
    · exact quarter_015_017_valid
    · exact quarter_015_018_valid
    · exact quarter_015_019_valid
    · exact quarter_015_020_valid
    · exact quarter_015_021_valid
    · exact quarter_015_022_valid
    · exact quarter_015_023_valid
    · exact quarter_015_024_valid
    · exact quarter_015_025_valid
    · exact quarter_015_026_valid
    · exact quarter_015_027_valid
    · exact quarter_015_028_valid
    · exact quarter_015_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
