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

def quarter_023_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 1, 0, 2, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(102465129/100000000), 0, (19192791/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(560543/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-9336687063886503438164777/457463486508250000000000), (-64079547/560543), (-40663458022347003438164777/228731743254125000000000), (-64079547/560543), (-71990228980807503438164777/457463486508250000000000)]
    bernstein := [(703685342559292178019903367/1873770440737792000000000000), (1875854259774222321528801499/4684426101844480000000000000), (14277826683957307031840585677/35133195763833600000000000000), (11531305198752544833786737987/29277663136528000000000000000), (26588901590914354362542792023/73194157841320000000000000000)]
    reserve := (36326535307/100000000000) }

theorem quarter_023_000_valid : quarter_023_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_023_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_023_000]
  · intro i; fin_cases i <;> norm_num [quarter_023_000]
  · norm_num [quarter_023_000]
  · norm_num [quarter_023_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_023_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_023_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_023_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_023_000]

def quarter_023_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(100371721/100000000), 0, (19887081/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(71153/12500000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-8208487042318949692827207/464548117886000000000000), (-60597559/569224), (-40668488900274449692827207/232274058943000000000000), (-60597559/569224), (-73128490758229949692827207/464548117886000000000000)]
    bernstein := [(25542887225243746976342241593/74327698861760000000000000000), (54783549554092372087240394787/148655397723520000000000000000), (111418677708706730449600452033/297310795447040000000000000000), (215717198152734591859305697947/594621590894080000000000000000), (396003581849212929304558675273/1189243181788160000000000000000)]
    reserve := (83246973351/250000000000) }

theorem quarter_023_001_valid : quarter_023_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_023_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_023_001]
  · intro i; fin_cases i <;> norm_num [quarter_023_001]
  · norm_num [quarter_023_001]
  · norm_num [quarter_023_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_023_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_023_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_023_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_023_001]

def quarter_023_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 1, 0, 2, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(19608541/20000000), 0, (41103203/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(577517/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-1426099006298046362438957/94263219891350000000000), (-56939502/577517), (-8135027509922696362438957/47131609945675000000000), (-56939502/577517), (-14843956013547346362438957/94263219891350000000000)]
    bernstein := [(74943659209813187891663083523/241313842921856000000000000000), (20236252696962981297167944413/60328460730464000000000000000), (15471642832850517916961408309/45246345547848000000000000000), (1246171032223673960933468593/3770528795654000000000000000), (284174818686034867862751883/942632198913500000000000000)]
    reserve := (301469458621/1000000000000) }

theorem quarter_023_002_valid : quarter_023_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_023_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_023_002]
  · intro i; fin_cases i <;> norm_num [quarter_023_002]
  · norm_num [quarter_023_002]
  · norm_num [quarter_023_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_023_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_023_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_023_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_023_002]

def quarter_023_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(47737769/50000000), 0, (84730841/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(585377/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-9773973405635598256572169/764369130194800000000000), (-106220235/1170754), (-65093570208929798256572169/382184565097400000000000), (-106220235/1170754), (-120413167012223998256572169/764369130194800000000000)]
    bernstein := [(2111975726260626713666060111/7643691301948000000000000000), (9208591601509896784563339707/30574765207792000000000000000), (37663862899051992598321534059/122299060831168000000000000000), (145308269583885004690215666383/489196243324672000000000000000), (525814725929969699756030396871/1956784973298688000000000000000)]
    reserve := (16794599723/62500000000) }

theorem quarter_023_003_valid : quarter_023_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_023_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_023_003]
  · intro i; fin_cases i <;> norm_num [quarter_023_003]
  · norm_num [quarter_023_003]
  · norm_num [quarter_023_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_023_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_023_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_023_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_023_003]

def quarter_023_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 1, 0, 2, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(231673/250000), 0, (21776787/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(592757/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-8238678976211038309129793/774005730506800000000000), (-49115626/592757), (-65109733826768638309129793/387002865253400000000000), (-49115626/592757), (-121980788677326238309129793/774005730506800000000000)]
    bernstein := [(477272706590133896248704771087/1981454670097408000000000000000), (52661339155095844167884088237/198145467009740800000000000000), (16217359561567344995261091973/59443640102922240000000000000), (519868938481048435359691749/1981454670097408000000000000), (46506272043574728661489823/198145467009740800000000000)]
    reserve := (9388309053/40000000000) }

theorem quarter_023_004_valid : quarter_023_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_023_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_023_004]
  · intro i; fin_cases i <;> norm_num [quarter_023_004]
  · norm_num [quarter_023_004]
  · norm_num [quarter_023_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_023_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_023_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_023_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_023_004]

def quarter_023_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(22406079/25000000), 0, (44660553/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(299807/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-17030661182269892909521343/1957398529634000000000000), (-44963763/599614), (-162821954872612892909521343/978699264817000000000000), (-44963763/599614), (-308613248562955892909521343/1957398529634000000000000)]
    bernstein := [(102349856194342949148331873/501094023586304000000000000), (1148422154004984670945181561/5010940235863040000000000000), (826745766726247431323963401/3496004815718400000000000000), (113485721831883046226991188473/501094023586304000000000000000), (999296720257540176098060282977/5010940235863040000000000000000)]
    reserve := (99711498563/500000000000) }

theorem quarter_023_005_valid : quarter_023_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_023_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_023_005]
  · intro i; fin_cases i <;> norm_num [quarter_023_005]
  · norm_num [quarter_023_005]
  · norm_num [quarter_023_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_023_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_023_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_023_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_023_005]

def quarter_023_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 1, 0, 2, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(345373/400000), 0, (22839737/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(37869/6250000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-1719924153567237495332851/247241475078000000000000), (-847162/12623), (-20359610527228987495332851/123620737539000000000000), (-847162/12623), (-12999765633630245831777617/82413825026000000000000)]
    bernstein := [(8102730097404880342365201953/48687552015360000000000000000), (15141896346211681502204791021/79117272024960000000000000000), (113495363872629455994497791/570557250180000000000000000), (39006384597562700060214611/206034562565000000000000000), (483828052294162560672937/2971652344687500000000000)]
    reserve := (40703621771/250000000000) }

theorem quarter_023_006_valid : quarter_023_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_023_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_023_006]
  · intro i; fin_cases i <;> norm_num [quarter_023_006]
  · norm_num [quarter_023_006]
  · norm_num [quarter_023_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_023_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_023_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_023_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_023_006]

def quarter_023_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(82830189/100000000), 0, (93207547/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(611587/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-2160864767049455192679741/399296712399400000000000), (-72452831/1223174), (-32587825353125155192679741/199648356199700000000000), (-72452831/1223174), (-63014785939200855192679741/399296712399400000000000)]
    bernstein := [(7944486300681222437123771/62390111312406250000000000), (152061772474782676498816969/998241780998500000000000000), (1917553159418961854195085037/11978901371982000000000000000), (19273738542380305840119167837/127774947967808000000000000000), (127591957454070811210055593059/1022199583742464000000000000000)]
    reserve := (15602622947/125000000000) }

theorem quarter_023_007_valid : quarter_023_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_023_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_023_007]
  · intro i; fin_cases i <;> norm_num [quarter_023_007]
  · norm_num [quarter_023_007]
  · norm_num [quarter_023_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_023_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_023_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_023_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_023_007]

def quarter_023_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 1, 0, 2, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(39545593/50000000), 0, (4742731/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(616623/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-16370826726713111514700481/4025846473026000000000000), (-31663876/616623), (-108672396249311037171566827/670974412171000000000000), (-31663876/616623), (-635663550769153111514700481/4025846473026000000000000)]
    bernstein := [(895909533610578656114937364319/10306166970946560000000000000000), (576888836997731191164562508251/5153083485473280000000000000000), (308891134286058906651146355479/2576541742736640000000000000000), (142956559643048917590240185491/1288270871368320000000000000000), (54986761533290832709388837839/644135435684160000000000000000)]
    reserve := (10670652181/125000000000) }

theorem quarter_023_008_valid : quarter_023_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_023_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_023_008]
  · intro i; fin_cases i <;> norm_num [quarter_023_008]
  · norm_num [quarter_023_008]
  · norm_num [quarter_023_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_023_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_023_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_023_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_023_008]

def quarter_023_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 1, 0, 2, 0, 0, 3]
    lambda := ![(8860113/50000000), (3108099/20000000), (7796359/100000000), (2702649/20000000), (2702649/20000000), (2702649/20000000), (1150199/6250000)]
    cone := fun i => (![![(4966969/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4167559/50000000), 0, 0]] i.1) i.2
    mu := ![(2857/2500000), (1360493/100000000), (219661/5000000), (3942059/100000000), (1/100000000), (1/100000000), (8335119/100000000)]
    alternative := .zero
    polynomial := [(-987705117789143983651310682859832750531/2157998212649172462273899337000000000000), (-2967499373953/357125000000), (-33961976799955360335797961796301290568531/1078999106324586231136949668500000000000), (-2967499373953/357125000000), (-3937426381301269216937918406455455787443/126941071332304262486699961000000000000)]
    bernstein := [(32063028866418139812101741667171200589667789/345279714023867593963823893920000000000000000), (13680705841250432438206106630263741631433823/138111885609547037585529557568000000000000000), (16892311505784228238872338398847383000189087/165734262731456445102635469081600000000000000), (34509366891227269850781214058250151637047/339967718423500400210534295552000000000000), (2660844717596670641570326072966562290297/27197417473880032016842743644160000000000)]
    reserve := (92861027057/1000000000000) }

theorem quarter_023_009_valid : quarter_023_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_023_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_023_009]
  · intro i; fin_cases i <;> norm_num [quarter_023_009]
  · norm_num [quarter_023_009]
  · norm_num [quarter_023_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_023_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_023_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_023_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_023_009]

def quarter_023_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 1, 0, 2, 0, 0, 3]
    lambda := ![(8719607/50000000), (15664633/100000000), (3943167/50000000), (13707839/100000000), (13707839/100000000), (13707839/100000000), (17886303/100000000)]
    cone := fun i => (![![(3974121/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8250951/100000000), 0, 0]] i.1) i.2
    mu := ![(111723/100000000), (1128893/100000000), (138483/3125000), (1998007/50000000), (1/100000000), (1/100000000), (1031369/12500000)]
    alternative := .zero
    polynomial := [(-22914875631627089899061705690518670581/86078913409602296329440254400000000000), (-24860843983327/3724100000000), (-1328697865959358911963396761244444206581/43039456704801148164720127200000000000), (-24860843983327/3724100000000), (-2634480856287090734027731816798369742581/86078913409602296329440254400000000000)]
    bernstein := [(1289701429113929839061631515254076499011/14103169173029240230615491280896000000000), (318301608258247012333587415704870168941/3264622493756768571901734092800000000000), (165765711004161640231952624675051778847853/1652715137464364089525252884480000000000000), (2547363382369367959719314196566624485957/25504863232474754467982297600000000000000), (82857518009067566430992113187321566811219/860789134096022963294402544000000000000000)]
    reserve := (45723816161/500000000000) }

theorem quarter_023_010_valid : quarter_023_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_023_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_023_010]
  · intro i; fin_cases i <;> norm_num [quarter_023_010]
  · norm_num [quarter_023_010]
  · norm_num [quarter_023_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_023_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_023_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_023_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_023_010]

def quarter_023_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 3]
    lambda := ![(17109551/100000000), (7870491/50000000), (3987639/50000000), (6966771/50000000), (6966771/50000000), (6966771/50000000), (17373563/100000000)]
    cone := fun i => (![![(377159/12500000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (817599/10000000), 0, 0]] i.1) i.2
    mu := ![(4361/4000000), (447379/50000000), (557351/12500000), (811333/20000000), (1/100000000), (1/100000000), (8175991/100000000)]
    alternative := .zero
    polynomial := [(-29670668292178537355364872256994980627/248732201258920386577170083000000000000), (-13963271576309/2725625000000), (-3794820998643563273719796966836045093427/124366100629460193288585041500000000000), (-13963271576309/2725625000000), (-7559971328994948010084229061415095206227/248732201258920386577170083000000000000)]
    bernstein := [(2215416419916811464299714256059197563073/24626950619695087779917830000000000000000), (9445070291612926403997003947586240654519/98507802478780351119671320000000000000000), (11771463251128884872776371117520968452062771/119391456604281785557041639840000000000000000), (15620978326802804134468966404778053810345071/159188608805709047409388853120000000000000000), (60171199727966303155462624750839681576734013/636754435222836189637555412480000000000000000)]
    reserve := (89959023109/1000000000000) }

theorem quarter_023_011_valid : quarter_023_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_023_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_023_011]
  · intro i; fin_cases i <;> norm_num [quarter_023_011]
  · norm_num [quarter_023_011]
  · norm_num [quarter_023_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_023_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_023_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_023_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_023_011]

def quarter_023_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 1, 0, 2, 0, 0, 3]
    lambda := ![(1673123/10000000), (15765763/100000000), (8062561/100000000), (1774083/12500000), (1774083/12500000), (1774083/12500000), (3372491/20000000)]
    cone := fun i => (![![(419921/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8110183/100000000), 0, 0]] i.1) i.2
    mu := ![(5309/5000000), (330277/50000000), (4474393/100000000), (4124467/100000000), (1/100000000), (1/100000000), (1013773/12500000)]
    alternative := .zero
    polynomial := [(-181612222056039496062545501769973449703/13121809492817826529317520223600000000000), (-7750502452191/2123600000000), (-200710448234915916843461933561727190494703/6560904746408913264658760111800000000000), (-7750502452191/2123600000000), (-401239284247775794190861321621684407539703/13121809492817826529317520223600000000000)]
    bernstein := [(2968841060122163189677787742300892652670437657/33591832301613635915052851772416000000000000000), (143813797694140213266967079440422937107659729/1526901468255165268866038716928000000000000000), (128336161278266078533881041243910146080974401/1325993380326854049278402043648000000000000000), (36720494098383194810932764958676577597979081/381725367063791317216509679232000000000000000), (194055581625773027394971211469657327411037897/2099489518850852244690803235776000000000000000)]
    reserve := (88379848811/1000000000000) }

theorem quarter_023_012_valid : quarter_023_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_023_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_023_012]
  · intro i; fin_cases i <;> norm_num [quarter_023_012]
  · norm_num [quarter_023_012]
  · norm_num [quarter_023_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_023_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_023_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_023_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_023_012]

def quarter_023_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 3]
    lambda := ![(8152541/50000000), (393387/2500000), (407359/5000000), (2897417/20000000), (2897417/20000000), (2897417/20000000), (3270201/20000000)]
    cone := fun i => (![![(1224603/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1610701/20000000), 0, 0]] i.1) i.2
    mu := ![(20637/20000000), (42909/10000000), (1119343/25000000), (4199753/100000000), (1/100000000), (1/100000000), (4026753/50000000)]
    alternative := .zero
    polynomial := [(65949971657122237269123870847175148067/1241661218056579410262779546000000000000), (-517129350747/229300000000), (-19686943689299719663024033667245584551933/620830609028289705131389773000000000000), (-517129350747/229300000000), (-39439837350256561563317191205338344251933/1241661218056579410262779546000000000000)]
    bernstein := [(17221080334096806047865463038571611491721667/198665794889052705642044727360000000000000000), (4079317274859719553217688175993462574263163/44147954419789490142676606080000000000000000), (226004212467185762971268050086818221866432601/2383989538668632467704536728320000000000000000), (16581804495900198768315443396552341580418763/176591817679157960570706424320000000000000000), (285122873944028285547850992734988918034682467/3178652718224843290272715637760000000000000000)]
    reserve := (21670917663/250000000000) }

theorem quarter_023_013_valid : quarter_023_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_023_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_023_013]
  · intro i; fin_cases i <;> norm_num [quarter_023_013]
  · norm_num [quarter_023_013]
  · norm_num [quarter_023_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_023_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_023_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_023_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_023_013]

def quarter_023_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 1, 0, 2, 0, 0, 3]
    lambda := ![(7916403/50000000), (15647023/100000000), (8227737/100000000), (7409113/50000000), (7409113/50000000), (7409113/50000000), (3167551/20000000)]
    cone := fun i => (![![(197941/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8005947/100000000), 0, 0]] i.1) i.2
    mu := ![(2501/2500000), (204261/100000000), (1116743/25000000), (171309/4000000), (1/100000000), (1/100000000), (8005947/100000000)]
    alternative := .zero
    polynomial := [(358004282241390545155781521771505851/4240810871346693497049282000000000000), (-37602153947/40016000000), (-78508359820003562809340950561990456649/2120405435673346748524641000000000000), (-37602153947/40016000000), (-157374723922248516163837682645752419149/4240810871346693497049282000000000000)]
    bernstein := [(920306017531997175397862667621208399864051/10856475830647535352446161920000000000000000), (2455493181876956955316581255099426016679/27141189576618838381115404800000000000000), (1879011989887425922119344318370190128151/20355892182464128785836553600000000000000), (1531642043527543375698515238931420279/16963243485386773988197128000000000000), (358004282241390545155781521771505851/4240810871346693497049282000000000000)]
    reserve := (5276176731/62500000000) }

theorem quarter_023_014_valid : quarter_023_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_023_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_023_014]
  · intro i; fin_cases i <;> norm_num [quarter_023_014]
  · norm_num [quarter_023_014]
  · norm_num [quarter_023_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_023_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_023_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_023_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_023_014]

def quarter_023_015 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 3]
    lambda := ![(15664929/100000000), (626793/4000000), (8185453/100000000), (7330851/50000000), (7330851/50000000), (7330851/50000000), (515459/3125000)]
    cone := fun i => (![![0, 0, (412303/50000000), 0, 0], ![(97921/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8136631/100000000), 0, 0]] i.1) i.2
    mu := ![(104189/100000000), (98979/100000000), (1116779/25000000), (1060743/25000000), (1/100000000), (1/100000000), (8136631/100000000)]
    alternative := .zero
    polynomial := [(2540890523799880658332104536119770625649/33133377688326155262946323039000000000000), (137734455890262551/85937691925000000), (-840791274226010051178249199787289199399351/16566688844163077631473161519500000000000), (137734455890262551/85937691925000000), (-1684123438975819983014830504110698169424351/33133377688326155262946323039000000000000)]
    bernstein := [(2540890523799880658332104536119770625649/33133377688326155262946323039000000000000), (2872788527856917721455659809160349064899/33133377688326155262946323039000000000000), (14541704078960972914801983194777162820515849/159040212903965545262142350587200000000000000), (4818075881331633942209306923872160888478299/53013404301321848420714116862400000000000000), (7213223248735511065165972092326159585345292449/84821446882114957473142586979840000000000000000)]
    reserve := (3067469363/40000000000) }

theorem quarter_023_015_valid : quarter_023_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_023_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_023_015]
  · intro i; fin_cases i <;> norm_num [quarter_023_015]
  · norm_num [quarter_023_015]
  · norm_num [quarter_023_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_023_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_023_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_023_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_023_015]

def quarter_023_016 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 1, 0, 2, 0, 0, 3]
    lambda := ![(8102981/50000000), (8125803/50000000), (1037251/12500000), (14588551/100000000), (14588551/100000000), (14588551/100000000), (15478771/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1217159/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (981527/12500000), 0, 0]] i.1) i.2
    mu := ![(439913/100000000), (51279/50000000), (4610781/100000000), (66263/1562500), (1/100000000), (1/100000000), (981527/12500000)]
    alternative := .zero
    polynomial := [(1978838902419332332171497716522597360657/36078868708515857865523461264000000000000), (765191069993/341860000000), (-564145758035803105154497038863025014799343/18039434354257928932761730632000000000000), (765191069993/341860000000), (-1130270354974025542641165575442572626959343/36078868708515857865523461264000000000000)]
    bernstein := [(8431041760569994981622915363192028589025063057/92361903893800596135740060835840000000000000000), (490099784050870605939728649449624318034175273/5131216882988922007541114490880000000000000000), (954874026025039359964901960068756127158854053/9895918274335778157400720803840000000000000000), (120858381106143357669869253808845521156007673/1282804220747230501885278622720000000000000000), (511830045119049841961421347793915419302686257/5772618993362537258483753802240000000000000000)]
    reserve := (88665135479/1000000000000) }

theorem quarter_023_016_valid : quarter_023_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_023_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_023_016]
  · intro i; fin_cases i <;> norm_num [quarter_023_016]
  · norm_num [quarter_023_016]
  · norm_num [quarter_023_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_023_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_023_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_023_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_023_016]

def quarter_023_017 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 3]
    lambda := ![(10337/62500), (416723/2500000), (832571/10000000), (898749/6250000), (898749/6250000), (898749/6250000), (15326219/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(518877/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1939477/25000000), 0, 0]] i.1) i.2
    mu := ![(675313/100000000), (52481/50000000), (2354031/50000000), (4198607/100000000), (1/100000000), (1/100000000), (1939477/25000000)]
    alternative := .zero
    polynomial := [(-6939408291714083248402622576344105528423/679374510924303314632245811077000000000000), (9453454502179/2624050000000), (-784932362117767352350075254098946240117571/26129788881703973639701761964500000000000), (9453454502179/2624050000000), (-20401302006770237077853553983996258137528423/679374510924303314632245811077000000000000)]
    bernstein := [(10335171917156908707077105004393356211829253177/108699921747888530341159329772320000000000000000), (294521415177375934897943949047273173072226147/2978080047887356995648200815680000000000000000), (129909270342530037904046396160396665909580912179/1304399060974662364093911957267840000000000000000), (1157410858428374113936127820662651744131541323/11912320191549427982592803262720000000000000000), (159272652459763053677613009333967727945487535337/1739198747966216485458549276357120000000000000000)]
    reserve := (45789088983/500000000000) }

theorem quarter_023_017_valid : quarter_023_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_023_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_023_017]
  · intro i; fin_cases i <;> norm_num [quarter_023_017]
  · norm_num [quarter_023_017]
  · norm_num [quarter_023_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_023_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_023_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_023_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_023_017]

def quarter_023_018 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 1, 0, 2, 0, 0, 3]
    lambda := ![(1050327/6250000), (4266137/25000000), (8360119/100000000), (14219669/100000000), (14219669/100000000), (14219669/100000000), (1888887/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1481803/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (382993/5000000), 0, 0]] i.1) i.2
    mu := ![(454251/50000000), (53543/50000000), (4801521/100000000), (4167999/100000000), (1/100000000), (1/100000000), (7659861/100000000)]
    alternative := .zero
    polynomial := [(-100516346441783244250662726545235013649/896688160360728541311311536500000000000), (269044852463/53543000000), (-13360277408506878938806666923896734453649/448344080180364270655655768250000000000), (269044852463/53543000000), (-26620038470571974633362671121248233893649/896688160360728541311311536500000000000)]
    bernstein := [(225708799861657579850495963958154038068083231/2295521690523465065756957533440000000000000000), (58542165086366871650057252037320901357609877/573880422630866266439239383360000000000000000), (44162587858919958668387914045536775519213777/430410316973149699829429537520000000000000000), (3590147212060184877624644530351874396054753/35867526414429141652452461460000000000000000), (8731237769157153908637341183986878390583/92442078387703973331063045000000000000000)]
    reserve := (47225451447/500000000000) }

theorem quarter_023_018_valid : quarter_023_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_023_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_023_018]
  · intro i; fin_cases i <;> norm_num [quarter_023_018]
  · norm_num [quarter_023_018]
  · norm_num [quarter_023_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_023_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_023_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_023_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_023_018]

def quarter_023_019 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 1, 0, 2, 0, 0, 3]
    lambda := ![(8502533/50000000), (68129/390625), (8402181/100000000), (3526113/25000000), (3526113/25000000), (3526113/25000000), (14838373/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(775037/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1889637/25000000), 0, 0]] i.1) i.2
    mu := ![(227257/20000000), (108941/100000000), (4891731/100000000), (2074179/50000000), (1/100000000), (1/100000000), (7558549/100000000)]
    alternative := .zero
    polynomial := [(-159954554898417660902020233084805124304859/632899284430016186687485651179000000000000), (35410104487713/5447050000000), (-9477838028918663206188018405535835656230859/316449642215008093343742825589500000000000), (35410104487713/5447050000000), (-18795721502938908751474016577986866188156859/632899284430016186687485651179000000000000)]
    bernstein := [(641577137219815452578424239523173905946481341/6328992844300161866874856511790000000000000000), (177278149386346338398461330758762645155115507/1687731425146709831166628403144000000000000000), (1283279014557882993168728402638932788098280867/12151666261056310784399724502636800000000000000), (1712412751370388595787349572397638041514007/16617663262982989106871418123264000000000000), (776385536895701673862631590907424769570433/7976478366231834771298280699166720000000000)]
    reserve := (24333593763/250000000000) }

theorem quarter_023_019_valid : quarter_023_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_023_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_023_019]
  · intro i; fin_cases i <;> norm_num [quarter_023_019]
  · norm_num [quarter_023_019]
  · norm_num [quarter_023_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_023_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_023_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_023_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_023_019]

def quarter_023_020 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 1, 0, 2, 0, 0, 3]
    lambda := ![(4285133/25000000), (4450287/25000000), (8452479/100000000), (112247/800000), (112247/800000), (112247/800000), (2902643/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(4804481/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (7454417/100000000), 0, 0]] i.1) i.2
    mu := ![(677999/50000000), (55271/50000000), (995861/20000000), (4138941/100000000), (1/100000000), (1/100000000), (7454417/100000000)]
    alternative := .zero
    polynomial := [(-187828071474511157391764605801855188409/432858931306779821320422181050000000000), (2772934905289/345443750000), (-45911777089799086825680084348770019880363/1515006259573729374621477633675000000000), (2772934905289/345443750000), (-90508757679276595549617816456927053441863/3030012519147458749242955267350000000000)]
    bernstein := [(51801398510899960430161045061635936939553/496437251137119641475965791002624000000000), (670551641000775865467211725504862632591503/6205465639213995518449572387532800000000000), (25279964777069493945364760421668247049532051/232704961470524831941858964532480000000000000), (20565383902102376888018338254348202024855379/193920801225437359951549137110400000000000000), (48608707089741855126826544811366102205875497/484802003063593399878872842776000000000000000)]
    reserve := (25066267663/250000000000) }

theorem quarter_023_020_valid : quarter_023_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_023_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_023_020]
  · intro i; fin_cases i <;> norm_num [quarter_023_020]
  · norm_num [quarter_023_020]
  · norm_num [quarter_023_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_023_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_023_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_023_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_023_020]

def quarter_023_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 3]
    lambda := ![(1721419/10000000), (4536993/25000000), (1063909/12500000), (13995221/100000000), (13995221/100000000), (13995221/100000000), (7070451/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(5746351/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3673937/50000000), 0, 0]] i.1) i.2
    mu := ![(782681/50000000), (22381/20000000), (5064899/100000000), (2069463/50000000), (1/100000000), (1/100000000), (58783/800000)]
    alternative := .zero
    polynomial := [(-81556616711710300659621546633869586107/124058129257176012054931313000000000000), (13431186540849/1398812500000), (-1909667186965982834603943310085732076107/62029064628588006027465656500000000000), (13431186540849/1398812500000), (-3737777757220255368548265073537594566107/124058129257176012054931313000000000000)]
    bernstein := [(2130317272341752060678422702875475164334933/19849300681148161928789010080000000000000000), (4411299097719469607707995834278656518376577/39698601362296323857578020160000000000000000), (26614201899582585880037626697778766011652039/238191608173777943145468120960000000000000000), (17330095409176187483816325189883531091926297/158794405449185295430312080640000000000000000), (32799905068546587050662143122673989006319493/317588810898370590860624161280000000000000000)]
    reserve := (103277898789/1000000000000) }

theorem quarter_023_021_valid : quarter_023_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_023_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_023_021]
  · intro i; fin_cases i <;> norm_num [quarter_023_021]
  · norm_num [quarter_023_021]
  · norm_num [quarter_023_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_023_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_023_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_023_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_023_021]

def quarter_023_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 1, 0, 2, 0, 0, 3]
    lambda := ![(8614611/50000000), (18484793/100000000), (171571/2000000), (13993561/100000000), (13993561/100000000), (13993561/100000000), (13726751/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(3348189/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1809821/25000000), 0, 0]] i.1) i.2
    mu := ![(176247/10000000), (113051/100000000), (2574607/50000000), (4147427/100000000), (1/100000000), (1/100000000), (1809821/25000000)]
    alternative := .zero
    polynomial := [(-356135822473550699402679899862894748306259/385053842072462096592729745893000000000000), (31721201758589/2826275000000), (-6038203346820029367009125629957839026155259/192526921036231048296364872946500000000000), (31721201758589/2826275000000), (-11720270871166508034615571360052783304004259/385053842072462096592729745893000000000000)]
    bernstein := [(108786429591478993062799746724092438151455722941/985737835705502967277388149486080000000000000000), (1564429949602491521516511776274221399069318907/13690803273687541212185946520640000000000000000), (1327756120671022189703229285159416192313184213/11551615262173862897781892376790000000000000000), (924281372513072126094675044342141427939543/8227646198129531978477131322500000000000000), (37882156842217482574452397677657558220741/356003922034450902914875874531250000000000)]
    reserve := (5320469031/50000000000) }

theorem quarter_023_022_valid : quarter_023_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_023_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_023_022]
  · intro i; fin_cases i <;> norm_num [quarter_023_022]
  · norm_num [quarter_023_022]
  · norm_num [quarter_023_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_023_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_023_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_023_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_023_022]

def quarter_023_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 3]
    lambda := ![0, (7048811/25000000), (12519761/100000000), (3952333/20000000), (3952333/20000000), (3952333/20000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(2550639/20000000), 0, (12879439/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5160847/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (170837/100000000), (487197/6250000), (2955567/50000000), (1/100000000), (1/100000000), (322553/6250000)]
    alternative := .zero
    polynomial := [(-201196215727471493273380357114499663/105795494473468910254452000000000000), (808163880714421/42709250000000), (-2450033537434172402859374800093859663/52897747236734455127226000000000000), (808163880714421/42709250000000), (-4698870859140873312445369243073219663/105795494473468910254452000000000000)]
    bernstein := [(1825046639946318648505359930180956953/16530546011479517227258125000000000000), (2841756899663625012222682074624143239/24044430562152025057830000000000000000), (54961655162158865465686190854744487497/453409262029152472519080000000000000000), (8965251991263795661959635843809222523/75065539315986809936640000000000000000), (744777572884058246455196525936292246377/6605767459806839274424320000000000000000)]
    reserve := (22080899671/200000000000) }

theorem quarter_023_023_valid : quarter_023_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_023_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_023_023]
  · intro i; fin_cases i <;> norm_num [quarter_023_023]
  · norm_num [quarter_023_023]
  · norm_num [quarter_023_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_023_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_023_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_023_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_023_023]

def quarter_023_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 1, 0, 2, 0, 0, 3]
    lambda := ![0, (15591553/50000000), (6323983/50000000), (585093/3125000), (585093/3125000), (585093/3125000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(15413753/100000000), 0, (3481637/12500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4889589/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (186979/100000000), (2125703/25000000), (5709231/100000000), (1/100000000), (1/100000000), (4889589/100000000)]
    alternative := .zero
    polynomial := [(-4915354187788985281869230074454124137/1849243660872480171200830500000000000), (1093053478517523/46744750000000), (-3681957846398961565988186294334929549/71124756187403083507724250000000000), (1093053478517523/46744750000000), (-90815549818584015433823613578254044137/1849243660872480171200830500000000000)]
    bernstein := [(582271363504047466266347752471404837626743/4734063771833549238274126080000000000000000), (62374875524275078694049935073413761489807/473406377183354923827412608000000000000000), (1477212349508947183256562695060402368249/10924762550385113626786444800000000000000), (631016229137731101089709237058821788399/4734063771833549238274126080000000000000), (59594564974479882537198976792980836407/473406377183354923827412608000000000000)]
    reserve := (24599219257/200000000000) }

theorem quarter_023_024_valid : quarter_023_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_023_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_023_024]
  · intro i; fin_cases i <;> norm_num [quarter_023_024]
  · norm_num [quarter_023_024]
  · norm_num [quarter_023_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_023_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_023_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_023_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_023_024]

def quarter_023_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 3]
    lambda := ![0, (2145573/6250000), (12687997/100000000), (3532189/20000000), (3532189/20000000), (3532189/20000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1147259/6250000), 0, (747579/2500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (922447/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (203489/100000000), (4623901/50000000), (5494813/100000000), (1/100000000), (1/100000000), (922447/20000000)]
    alternative := .zero
    polynomial := [(-25785144665641513816090628983590574537/7153771489222046126842618500000000000), (18088238157489/635903125000), (-206229995213786382146240587330168174537/3576885744611023063421309250000000000), (18088238157489/635903125000), (-386674845761931250476390545676745774537/7153771489222046126842618500000000000)]
    bernstein := [(250202245775264553952902255026224118807/1831365501240843808471710336000000000000), (81271322774348552455884526284703184877/554959242800255699536881920000000000000), (82617773309287561302484740320508689818157/549409650372253142541513100800000000000000), (6964376853621062256305862481288089714147/46958089775406251499274624000000000000000), (2566278703406946312737455935480584460357383/18313655012408438084717103360000000000000000)]
    reserve := (8538787233/62500000000) }

theorem quarter_023_025_valid : quarter_023_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_023_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_023_025]
  · intro i; fin_cases i <;> norm_num [quarter_023_025]
  · norm_num [quarter_023_025]
  · norm_num [quarter_023_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_023_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_023_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_023_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_023_025]

def quarter_023_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 1, 0, 2, 0, 0, 3]
    lambda := ![0, (18804687/50000000), (12636607/100000000), (16584673/100000000), (16584673/100000000), (16584673/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(539193/2500000), 0, (31866739/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4331161/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (220157/100000000), (10025217/100000000), (1053691/20000000), (1/100000000), (1/100000000), (2165581/50000000)]
    alternative := .zero
    polynomial := [(-96006474147084764519340222304861277519/20145310930854737130729996000000000000), (7512240425467107/220157000000000), (-644340515908516756927289768215599317519/10072655465427368565364998000000000000), (7512240425467107/220157000000000), (-1192674557669948749335239314126337357519/20145310930854737130729996000000000000)]
    bernstein := [(7801316911545547748068607493498256831607521/51571995982988127054668789760000000000000000), (2091795085395218510759169456677210009973833/12892998995747031763667197440000000000000000), (1611808194748241071323752035674545338068727/9669749246810273822750398080000000000000000), (132538462581742034496067422917615069625757/805812437234189485229199840000000000000000), (31321078004697363374851420700574156236761/201453109308547371307299960000000000000000)]
    reserve := (151270408733/1000000000000) }

theorem quarter_023_026_valid : quarter_023_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_023_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_023_026]
  · intro i; fin_cases i <;> norm_num [quarter_023_026]
  · norm_num [quarter_023_026]
  · norm_num [quarter_023_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_023_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_023_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_023_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_023_026]

def quarter_023_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 1, 0, 2, 0, 0, 3]
    lambda := ![0, (20495427/50000000), (1561703/12500000), (7752587/50000000), (7752587/50000000), (7752587/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(25024843/100000000), 0, (8424277/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2024623/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (236729/100000000), (10827981/100000000), (5031449/100000000), (1/100000000), (1/100000000), (2024623/50000000)]
    alternative := .zero
    polynomial := [(-80489331281251106827131520541818785077/13055881332353702135909161500000000000), (1195907530091763/29591125000000), (-461383506349101397216088653554802245077/6527940666176851067954580750000000000), (1195907530091763/29591125000000), (-842277681416951687605045786567785705077/13055881332353702135909161500000000000)]
    bernstein := [(21792983634787188684305715106064093460163/130558813323537021359091615000000000000000), (93542862077863728728279316435187781150473/522235253294148085436366460000000000000000), (1153829679201608531179587688939081565558749/6266823039529777025236397520000000000000000), (1518804570641983918373388836361181488157493/8355764052706369366981863360000000000000000), (5745449999566446995797052230197389975654203/33423056210825477467927453440000000000000000)]
    reserve := (166920815837/1000000000000) }

theorem quarter_023_027_valid : quarter_023_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_023_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_023_027]
  · intro i; fin_cases i <;> norm_num [quarter_023_027]
  · norm_num [quarter_023_027]
  · norm_num [quarter_023_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_023_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_023_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_023_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_023_027]

def quarter_023_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 1, 0, 2, 0, 0, 3]
    lambda := ![0, (44431431/100000000), (12262653/100000000), (7217653/50000000), (7217653/50000000), (7217653/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(5738317/20000000), 0, (17672229/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (753969/20000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (126457/50000000), (1164667/10000000), (239297/5000000), (1/100000000), (1/100000000), (753969/20000000)]
    alternative := .zero
    polynomial := [(-138565315647193650608806565762228021/17715121271399935234978000000000000), (11962879368651651/252914000000000), (-688552906435138945995660623751458021/8857560635699967617489000000000000), (11962879368651651/252914000000000), (-1238540497223084241382514681740688021/17715121271399935234978000000000000)]
    bernstein := [(8323130396103100359081521313661214675419/45350710454783834201543680000000000000000), (4467655404044495405240351640735632573241/22675355227391917100771840000000000000000), (6891608309763113604548031044147626563097/34013032841087875651157760000000000000000), (1134488683728111141363180081503949601761/5668838806847979275192960000000000000000), (536727856059392967864838972030467498379/2834419403423989637596480000000000000000)]
    reserve := (11470507177/62500000000) }

theorem quarter_023_028_valid : quarter_023_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_023_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_023_028]
  · intro i; fin_cases i <;> norm_num [quarter_023_028]
  · norm_num [quarter_023_028]
  · norm_num [quarter_023_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_023_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_023_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_023_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_023_028]

def quarter_023_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 1, 0, 2, 0, 0, 3]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(13583621/20000000), 0, (19192791/25000000), 0, 0], ![0, 0, (26115447/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (560543/100000000), (3264431/12500000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-225687117940091736631685173/10979123676198000000000000), (320397734/2802715), (-977529620943143736631685173/5489561838099000000000000), (320397734/2802715), (-1729372123946195736631685173/10979123676198000000000000)]
    bernstein := [(314235498496942627315637438027/1756659788191680000000000000000), (146182140136763496479577675463/702663915276672000000000000000), (184737751281415488041979179273/843196698332006400000000000000), (23792104293952627085543809151/112426226444267520000000000000), (8326718578362657089749713083/44970490577707008000000000000)]
    reserve := (44720597097/250000000000) }

theorem quarter_023_029_valid : quarter_023_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_023_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_023_029]
  · intro i; fin_cases i <;> norm_num [quarter_023_029]
  · norm_num [quarter_023_029]
  · norm_num [quarter_023_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_023_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_023_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_023_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_023_029]

def quarterTable023 : OwnerTable where
  mode := .quarter
  owners := ![0, 1, 0, 2, 0, 0, 3]
  rows := [quarter_023_000, quarter_023_001, quarter_023_002, quarter_023_003, quarter_023_004, quarter_023_005, quarter_023_006, quarter_023_007, quarter_023_008, quarter_023_009, quarter_023_010, quarter_023_011, quarter_023_012, quarter_023_013, quarter_023_014, quarter_023_015, quarter_023_016, quarter_023_017, quarter_023_018, quarter_023_019, quarter_023_020, quarter_023_021, quarter_023_022, quarter_023_023, quarter_023_024, quarter_023_025, quarter_023_026, quarter_023_027, quarter_023_028, quarter_023_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_023_000_valid
    · exact quarter_023_001_valid
    · exact quarter_023_002_valid
    · exact quarter_023_003_valid
    · exact quarter_023_004_valid
    · exact quarter_023_005_valid
    · exact quarter_023_006_valid
    · exact quarter_023_007_valid
    · exact quarter_023_008_valid
    · exact quarter_023_009_valid
    · exact quarter_023_010_valid
    · exact quarter_023_011_valid
    · exact quarter_023_012_valid
    · exact quarter_023_013_valid
    · exact quarter_023_014_valid
    · exact quarter_023_015_valid
    · exact quarter_023_016_valid
    · exact quarter_023_017_valid
    · exact quarter_023_018_valid
    · exact quarter_023_019_valid
    · exact quarter_023_020_valid
    · exact quarter_023_021_valid
    · exact quarter_023_022_valid
    · exact quarter_023_023_valid
    · exact quarter_023_024_valid
    · exact quarter_023_025_valid
    · exact quarter_023_026_valid
    · exact quarter_023_027_valid
    · exact quarter_023_028_valid
    · exact quarter_023_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
