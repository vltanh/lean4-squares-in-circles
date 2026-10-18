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

def quarter_035_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 2, 0, 2, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(102465129/100000000), 0, (19192791/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(560543/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-9336687063886503438164777/457463486508250000000000), (-64079547/560543), (-40663458022347003438164777/228731743254125000000000), (-64079547/560543), (-71990228980807503438164777/457463486508250000000000)]
    bernstein := [(703685342559292178019903367/1873770440737792000000000000), (1875854259774222321528801499/4684426101844480000000000000), (14277826683957307031840585677/35133195763833600000000000000), (11531305198752544833786737987/29277663136528000000000000000), (26588901590914354362542792023/73194157841320000000000000000)]
    reserve := (36326535307/100000000000) }

theorem quarter_035_000_valid : quarter_035_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_035_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_035_000]
  · intro i; fin_cases i <;> norm_num [quarter_035_000]
  · norm_num [quarter_035_000]
  · norm_num [quarter_035_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_035_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_035_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_035_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_035_000]

def quarter_035_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(100371721/100000000), 0, (19887081/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(71153/12500000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-8208487042318949692827207/464548117886000000000000), (-60597559/569224), (-40668488900274449692827207/232274058943000000000000), (-60597559/569224), (-73128490758229949692827207/464548117886000000000000)]
    bernstein := [(25542887225243746976342241593/74327698861760000000000000000), (54783549554092372087240394787/148655397723520000000000000000), (111418677708706730449600452033/297310795447040000000000000000), (215717198152734591859305697947/594621590894080000000000000000), (396003581849212929304558675273/1189243181788160000000000000000)]
    reserve := (83246973351/250000000000) }

theorem quarter_035_001_valid : quarter_035_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_035_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_035_001]
  · intro i; fin_cases i <;> norm_num [quarter_035_001]
  · norm_num [quarter_035_001]
  · norm_num [quarter_035_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_035_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_035_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_035_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_035_001]

def quarter_035_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 2, 0, 2, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(19608541/20000000), 0, (41103203/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(577517/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-1426099006298046362438957/94263219891350000000000), (-56939502/577517), (-8135027509922696362438957/47131609945675000000000), (-56939502/577517), (-14843956013547346362438957/94263219891350000000000)]
    bernstein := [(74943659209813187891663083523/241313842921856000000000000000), (20236252696962981297167944413/60328460730464000000000000000), (15471642832850517916961408309/45246345547848000000000000000), (1246171032223673960933468593/3770528795654000000000000000), (284174818686034867862751883/942632198913500000000000000)]
    reserve := (301469458621/1000000000000) }

theorem quarter_035_002_valid : quarter_035_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_035_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_035_002]
  · intro i; fin_cases i <;> norm_num [quarter_035_002]
  · norm_num [quarter_035_002]
  · norm_num [quarter_035_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_035_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_035_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_035_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_035_002]

def quarter_035_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(47737769/50000000), 0, (84730841/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(585377/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-9773973405635598256572169/764369130194800000000000), (-106220235/1170754), (-65093570208929798256572169/382184565097400000000000), (-106220235/1170754), (-120413167012223998256572169/764369130194800000000000)]
    bernstein := [(2111975726260626713666060111/7643691301948000000000000000), (9208591601509896784563339707/30574765207792000000000000000), (37663862899051992598321534059/122299060831168000000000000000), (145308269583885004690215666383/489196243324672000000000000000), (525814725929969699756030396871/1956784973298688000000000000000)]
    reserve := (16794599723/62500000000) }

theorem quarter_035_003_valid : quarter_035_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_035_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_035_003]
  · intro i; fin_cases i <;> norm_num [quarter_035_003]
  · norm_num [quarter_035_003]
  · norm_num [quarter_035_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_035_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_035_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_035_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_035_003]

def quarter_035_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 2, 0, 2, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(231673/250000), 0, (21776787/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(592757/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-8238678976211038309129793/774005730506800000000000), (-49115626/592757), (-65109733826768638309129793/387002865253400000000000), (-49115626/592757), (-121980788677326238309129793/774005730506800000000000)]
    bernstein := [(477272706590133896248704771087/1981454670097408000000000000000), (52661339155095844167884088237/198145467009740800000000000000), (16217359561567344995261091973/59443640102922240000000000000), (519868938481048435359691749/1981454670097408000000000000), (46506272043574728661489823/198145467009740800000000000)]
    reserve := (9388309053/40000000000) }

theorem quarter_035_004_valid : quarter_035_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_035_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_035_004]
  · intro i; fin_cases i <;> norm_num [quarter_035_004]
  · norm_num [quarter_035_004]
  · norm_num [quarter_035_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_035_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_035_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_035_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_035_004]

def quarter_035_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(22406079/25000000), 0, (44660553/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(299807/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-17030661182269892909521343/1957398529634000000000000), (-44963763/599614), (-162821954872612892909521343/978699264817000000000000), (-44963763/599614), (-308613248562955892909521343/1957398529634000000000000)]
    bernstein := [(102349856194342949148331873/501094023586304000000000000), (1148422154004984670945181561/5010940235863040000000000000), (826745766726247431323963401/3496004815718400000000000000), (113485721831883046226991188473/501094023586304000000000000000), (999296720257540176098060282977/5010940235863040000000000000000)]
    reserve := (99711498563/500000000000) }

theorem quarter_035_005_valid : quarter_035_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_035_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_035_005]
  · intro i; fin_cases i <;> norm_num [quarter_035_005]
  · norm_num [quarter_035_005]
  · norm_num [quarter_035_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_035_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_035_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_035_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_035_005]

def quarter_035_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 2, 0, 2, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(345373/400000), 0, (22839737/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(37869/6250000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-1719924153567237495332851/247241475078000000000000), (-847162/12623), (-20359610527228987495332851/123620737539000000000000), (-847162/12623), (-12999765633630245831777617/82413825026000000000000)]
    bernstein := [(8102730097404880342365201953/48687552015360000000000000000), (15141896346211681502204791021/79117272024960000000000000000), (113495363872629455994497791/570557250180000000000000000), (39006384597562700060214611/206034562565000000000000000), (483828052294162560672937/2971652344687500000000000)]
    reserve := (40703621771/250000000000) }

theorem quarter_035_006_valid : quarter_035_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_035_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_035_006]
  · intro i; fin_cases i <;> norm_num [quarter_035_006]
  · norm_num [quarter_035_006]
  · norm_num [quarter_035_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_035_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_035_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_035_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_035_006]

def quarter_035_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(82830189/100000000), 0, (93207547/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(611587/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-2160864767049455192679741/399296712399400000000000), (-72452831/1223174), (-32587825353125155192679741/199648356199700000000000), (-72452831/1223174), (-63014785939200855192679741/399296712399400000000000)]
    bernstein := [(7944486300681222437123771/62390111312406250000000000), (152061772474782676498816969/998241780998500000000000000), (1917553159418961854195085037/11978901371982000000000000000), (19273738542380305840119167837/127774947967808000000000000000), (127591957454070811210055593059/1022199583742464000000000000000)]
    reserve := (15602622947/125000000000) }

theorem quarter_035_007_valid : quarter_035_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_035_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_035_007]
  · intro i; fin_cases i <;> norm_num [quarter_035_007]
  · norm_num [quarter_035_007]
  · norm_num [quarter_035_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_035_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_035_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_035_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_035_007]

def quarter_035_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 2, 0, 2, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(39545593/50000000), 0, (4742731/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(616623/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-16370826726713111514700481/4025846473026000000000000), (-31663876/616623), (-108672396249311037171566827/670974412171000000000000), (-31663876/616623), (-635663550769153111514700481/4025846473026000000000000)]
    bernstein := [(895909533610578656114937364319/10306166970946560000000000000000), (576888836997731191164562508251/5153083485473280000000000000000), (308891134286058906651146355479/2576541742736640000000000000000), (142956559643048917590240185491/1288270871368320000000000000000), (54986761533290832709388837839/644135435684160000000000000000)]
    reserve := (10670652181/125000000000) }

theorem quarter_035_008_valid : quarter_035_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_035_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_035_008]
  · intro i; fin_cases i <;> norm_num [quarter_035_008]
  · norm_num [quarter_035_008]
  · norm_num [quarter_035_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_035_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_035_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_035_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_035_008]

def quarter_035_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 2, 0, 2, 0, 0, 3]
    lambda := ![(2280399/50000000), (1366373/10000000), (1366373/10000000), (330079/1562500), (330079/1562500), (330079/1562500), (74009/1562500)]
    cone := fun i => (![![(1278389/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6753881/100000000), 0, 0]] i.1) i.2
    mu := ![(14707/50000000), (3947523/100000000), (1/100000000), (6357127/100000000), (1/100000000), (1/100000000), (6753881/100000000)]
    alternative := .zero
    polynomial := [(-24492679141325815202104050208020001/712188586042052675404002000000000000), (-37564046702237881/17278637131250000), (-2737072645169328582463477249298940001/356094293021026337702001000000000000), (-37564046702237881/17278637131250000), (-778521801599618764246407206912837143/101741226577436096486286000000000000)]
    bernstein := [(13928351913605261581017384040929057972719/113950173766728428064640320000000000000000), (5596537987740303935479333988665759793333/45580069506691371225856128000000000000000), (6701977380622170734798349826819000420277/54696083408029645471027353600000000000000), (25312459996287219097998568933239021983/208366032030589125603913728000000000000), (13960167776881393185238113022769531831/116684977937129910338191687680000000000)]
    reserve := (119639803029/1000000000000) }

theorem quarter_035_009_valid : quarter_035_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_035_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_035_009]
  · intro i; fin_cases i <;> norm_num [quarter_035_009]
  · norm_num [quarter_035_009]
  · norm_num [quarter_035_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_035_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_035_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_035_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_035_009]

def quarter_035_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 2, 0, 2, 0, 0, 3]
    lambda := ![(60479/1250000), (13419551/100000000), (13419551/100000000), (21120073/100000000), (21120073/100000000), (21120073/100000000), (4962359/100000000)]
    cone := fun i => (![![(68911/6250000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (851443/12500000), 0, 0]] i.1) i.2
    mu := ![(30997/100000000), (1938643/50000000), (1/100000000), (395173/6250000), (1/100000000), (1/100000000), (851443/12500000)]
    alternative := .zero
    polynomial := [(305446243332731565288211707535931/40438062918176535944738000000000000), (-5606789559088142917/3004605853550000000), (-161732589580899099445282419856444069/20219031459088267972369000000000000), (-5606789559088142917/3004605853550000000), (-323770625405130930455853051420424069/40438062918176535944738000000000000)]
    bernstein := [(778591675899810778742673920074092339/6625372228514043649185873920000000000), (4894348455027983855994775995048635343/41408576428212772807411712000000000000), (91645812731207921023419722201632913597/776410808028989490138969600000000000000), (37865846463535822151614907887195031511/323504503345412287557904000000000000000), (46598824734685177915993470431955272131/404380629181765359447380000000000000000)]
    reserve := (57617528353/500000000000) }

theorem quarter_035_010_valid : quarter_035_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_035_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_035_010]
  · intro i; fin_cases i <;> norm_num [quarter_035_010]
  · norm_num [quarter_035_010]
  · norm_num [quarter_035_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_035_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_035_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_035_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_035_010]

def quarter_035_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 3]
    lambda := ![(2541747/50000000), (6584689/50000000), (6584689/50000000), (4227721/20000000), (4227721/20000000), (4227721/20000000), (322621/6250000)]
    cone := fun i => (![![(35859/4000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (858563/12500000), 0, 0]] i.1) i.2
    mu := ![(32393/100000000), (3796831/100000000), (1/100000000), (6293067/100000000), (1/100000000), (1/100000000), (858563/12500000)]
    alternative := .zero
    polynomial := [(14442603935315593346547801461330933/332259162606842841646171500000000000), (-291263110480525073/192173041535937500), (-1375083513187927986053274693976899067/166129581303421420823085750000000000), (-291263110480525073/192173041535937500), (-2764609630311171565453097189415129067/332259162606842841646171500000000000)]
    bernstein := [(375262297880746646591285761434699987533/3322591626068428416461715000000000000000), (1511649851006904391595583697402545785899/13290366504273713665846860000000000000000), (1066397510116416643059128725617353092123/9381435179487327293538960000000000000000), (23974130559199860337608047211057120472391/212645864068379418653549760000000000000000), (191436698650168728452530521605786926361/1725321412319508467777280000000000000000)]
    reserve := (27739280531/250000000000) }

theorem quarter_035_011_valid : quarter_035_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_035_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_035_011]
  · intro i; fin_cases i <;> norm_num [quarter_035_011]
  · norm_num [quarter_035_011]
  · norm_num [quarter_035_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_035_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_035_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_035_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_035_011]

def quarter_035_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 2, 0, 2, 0, 0, 3]
    lambda := ![(5295517/100000000), (516497/4000000), (516497/4000000), (1059043/5000000), (1059043/5000000), (1059043/5000000), (5337051/100000000)]
    cone := fun i => (![![(83067/12500000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6925271/100000000), 0, 0]] i.1) i.2
    mu := ![(33607/100000000), (3706497/100000000), (1/100000000), (1567023/25000000), (1/100000000), (1/100000000), (865659/12500000)]
    alternative := .zero
    polynomial := [(167932336933136309029288623429301/2346838055638924912383375000000000), (-14064568630275936067/12456424467900000000), (-357256832955585672521718741430583/41907822422123659149703125000000), (-14064568630275936067/12456424467900000000), (-20174314982445933970245538143541949/2346838055638924912383375000000000)]
    bernstein := [(651807722851392918820707733696129380931/6007905422435647775701440000000000000000), (109542533256033565386403119673470567709/1001317570405941295950240000000000000000), (3706833051475716295085315903059538569/33879165915990494975760000000000000000), (81513916548386950874071793032407427403/750988177804455971962680000000000000000), (40097991484790655907407384319419333851/375494088902227985981340000000000000000)]
    reserve := (3337102423/31250000000) }

theorem quarter_035_012_valid : quarter_035_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_035_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_035_012]
  · intro i; fin_cases i <;> norm_num [quarter_035_012]
  · norm_num [quarter_035_012]
  · norm_num [quarter_035_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_035_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_035_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_035_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_035_012]

def quarter_035_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 3]
    lambda := ![(2736843/50000000), (1580979/12500000), (1580979/12500000), (21247183/100000000), (21247183/100000000), (21247183/100000000), (2744551/50000000)]
    cone := fun i => (![![(82221/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (69823/1000000), 0, 0]] i.1) i.2
    mu := ![(433/1250000), (450837/12500000), (1/100000000), (6247947/100000000), (1/100000000), (1/100000000), (6982301/100000000)]
    alternative := .zero
    polynomial := [(341982464645887386057914390093591/3784955982355564306572000000000000), (-12362586020025007/17352215200000000), (-16551477224070290924879169579849409/1892477991177782153286000000000000), (-12362586020025007/17352215200000000), (-33444936912786469235816253549792409/3784955982355564306572000000000000)]
    bernstein := [(63069235108181895022324133318438140391/605592957176890289051520000000000000000), (42452957751033359851082119717758720597/403728638117926859367680000000000000000), (764835629797308879238528031017066465973/7267115486122683468618240000000000000000), (168646207800002853459469520687980226997/1614914552471707437470720000000000000000), (995166686252976887996505791931270858791/9689487314830244624824320000000000000000)]
    reserve := (102705814447/1000000000000) }

theorem quarter_035_013_valid : quarter_035_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_035_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_035_013]
  · intro i; fin_cases i <;> norm_num [quarter_035_013]
  · norm_num [quarter_035_013]
  · norm_num [quarter_035_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_035_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_035_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_035_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_035_013]

def quarter_035_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 2, 0, 2, 0, 0, 3]
    lambda := ![(5617393/100000000), (6187319/50000000), (6187319/50000000), (21338061/100000000), (21338061/100000000), (21338061/100000000), (5619149/100000000)]
    cone := fun i => (![![(140457/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1759999/25000000), 0, 0]] i.1) i.2
    mu := ![(17747/50000000), (437237/12500000), (1/100000000), (3116387/50000000), (1/100000000), (1/100000000), (1759999/25000000)]
    alternative := .zero
    polynomial := [(4200369675676650485518297492605579/42560396004454279525907000000000000), (-841534528269260989/3103858015600000000), (-190312049743155649913055015382846921/21280198002227139762953500000000000), (-841534528269260989/3103858015600000000), (-384824469161987950311628328258299421/42560396004454279525907000000000000)]
    bernstein := [(10882533444061770538173715578233359493379/108954613771402955586321920000000000000000), (55012220747988400180987118656986992957/544773068857014777931609600000000000000), (20663814477805333853828016242112482279/204289900821380541724353600000000000000), (34179917475663676528524082685001757/340483168035634236207256000000000000), (4200369675676650485518297492605579/42560396004454279525907000000000000)]
    reserve := (6168248639/62500000000) }

theorem quarter_035_014_valid : quarter_035_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_035_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_035_014]
  · intro i; fin_cases i <;> norm_num [quarter_035_014]
  · norm_num [quarter_035_014]
  · norm_num [quarter_035_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_035_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_035_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_035_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_035_014]

def quarter_035_015 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 3]
    lambda := ![(233203/4000000), (3062707/25000000), (3062707/25000000), (1058823/5000000), (1058823/5000000), (1058823/5000000), (6138889/100000000)]
    cone := fun i => (![![0, 0, (306897/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3566763/50000000), 0, 0]] i.1) i.2
    mu := ![(38777/100000000), (1714097/50000000), (1/100000000), (9659/156250), (1/100000000), (1/100000000), (3566763/50000000)]
    alternative := .zero
    polynomial := [(43303082110239292590499439720749/457979476164437922294600000000000), (1526219337648403773/2658701574760000000), (-2237576354776342629396963606459251/228989738082218961147300000000000), (1526219337648403773/2658701574760000000), (-265791517156642620669672156037603/26939969186143407193800000000000)]
    bernstein := [(43303082110239292590499439720749/457979476164437922294600000000000), (16344079149926400983055915370511/166537991332522880834400000000000), (221391319074132038888881891515435949/2198301485589302027014080000000000000), (299744195228153889469823266021749221/2931068647452402702685440000000000000), (7089844207749817554936458794542552797/68966321116527122416128000000000000000)]
    reserve := (47276225643/500000000000) }

theorem quarter_035_015_valid : quarter_035_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_035_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_035_015]
  · intro i; fin_cases i <;> norm_num [quarter_035_015]
  · norm_num [quarter_035_015]
  · norm_num [quarter_035_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_035_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_035_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_035_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_035_015]

def quarter_035_016 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 2, 0, 2, 0, 0, 3]
    lambda := ![(6178873/100000000), (12419389/100000000), (12419389/100000000), (21027549/100000000), (21027549/100000000), (21027549/100000000), (737463/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (7032173/100000000), 0, 0]] i.1) i.2
    mu := ![(167907/100000000), (3434503/100000000), (1/100000000), (617077/10000000), (1/100000000), (1/100000000), (7032173/100000000)]
    alternative := .zero
    polynomial := [(237835527862677359158296650925937399/2502428099485965737743941000000000000), (117262929542821/343450300000000), (-2789404418912890607562597132200032601/1251214049742982868871970500000000000), (117262929542821/343450300000000), (-5816644365688458574283490915326002601/2502428099485965737743941000000000000)]
    bernstein := [(654642464803265021186172078433243465914199/6406215934684072288624488960000000000000000), (110644924173952166626498271900304602308333/1067702655780678714770748160000000000000000), (503715160629893670137573522014357116846997/4804661951013054216468366720000000000000000), (28245716645517079999362732455528484768733/266925663945169678692687040000000000000000), (42668588228606975514340393956189329156599/400388495917754518039030560000000000000000)]
    reserve := (1596697429/15625000000) }

theorem quarter_035_016_valid : quarter_035_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_035_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_035_016]
  · intro i; fin_cases i <;> norm_num [quarter_035_016]
  · norm_num [quarter_035_016]
  · norm_num [quarter_035_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_035_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_035_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_035_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_035_016]

def quarter_035_017 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 3]
    lambda := ![(6509073/100000000), (6266161/50000000), (6266161/50000000), (2599919/12500000), (2599919/12500000), (2599919/12500000), (6028227/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3503071/50000000), 0, 0]] i.1) i.2
    mu := ![(266111/100000000), (3419621/100000000), (1/100000000), (613587/10000000), (1/100000000), (1/100000000), (7006143/100000000)]
    alternative := .zero
    polynomial := [(9212354324720172525655641969179393/100307023266311588016489000000000000), (767514387759/2137263125000), (-77309991192249294122621287180545607/50153511633155794008244500000000000), (767514387759/2137263125000), (-163832336709218760770898216330270607/100307023266311588016489000000000000)]
    bernstein := [(1700856020425850103810994270126528123793/16049123722609854082638240000000000000000), (3443207213887053774308976279070051734179/32098247445219708165276480000000000000000), (20877879468273455816011124741253762270011/192589484671318248991658880000000000000000), (14044136807676697809369501037038246449611/128392989780878832661105920000000000000000), (28298829400461345845017572076276748679233/256785979561757665322211840000000000000000)]
    reserve := (105978123779/1000000000000) }

theorem quarter_035_017_valid : quarter_035_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_035_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_035_017]
  · intro i; fin_cases i <;> norm_num [quarter_035_017]
  · norm_num [quarter_035_017]
  · norm_num [quarter_035_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_035_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_035_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_035_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_035_017]

def quarter_035_018 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 2, 0, 2, 0, 0, 3]
    lambda := ![(3417273/50000000), (6318713/50000000), (6318713/50000000), (321617/1562500), (321617/1562500), (321617/1562500), (6140139/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1395799/20000000), 0, 0]] i.1) i.2
    mu := ![(370001/100000000), (1698083/50000000), (1/100000000), (610307/10000000), (1/100000000), (1/100000000), (1395799/20000000)]
    alternative := .zero
    polynomial := [(294960761406010228320714932002611/3345130486618010907926993750000000), (16009616491593/42452075000000), (-4049561482470954334927973307868153/3345130486618010907926993750000000), (16009616491593/42452075000000), (-1086130560969241140812172059967691/836282621654502726981748437500000)]
    bernstein := [(235002190037473885217213354568481863729/2140883511435526981073276000000000000000), (237674371198434899051972998187642233647/2140883511435526981073276000000000000000), (11254018559030838968121149495339312167/100353914598540327237809812500000000000), (15139759977200367545259034746625497283/133805219464720436317079750000000000000), (953611217228831549713316071838386609/8362826216545027269817484375000000000)]
    reserve := (109768788811/1000000000000) }

theorem quarter_035_018_valid : quarter_035_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_035_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_035_018]
  · intro i; fin_cases i <;> norm_num [quarter_035_018]
  · norm_num [quarter_035_018]
  · norm_num [quarter_035_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_035_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_035_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_035_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_035_018]

def quarter_035_019 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 2, 0, 2, 0, 0, 3]
    lambda := ![(7154753/100000000), (6367569/50000000), (6367569/50000000), (10189949/50000000), (10189949/50000000), (10189949/50000000), (3117639/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (434417/6250000), 0, 0]] i.1) i.2
    mu := ![(478813/100000000), (3364427/100000000), (1/100000000), (6072337/100000000), (1/100000000), (1/100000000), (6950673/100000000)]
    alternative := .zero
    polynomial := [(5714019054298950428228100409832638157/67992305234455279513137951000000000000), (66536521061163/168221350000000), (-34619725652035386831847536831094831843/33996152617227639756568975500000000000), (66536521061163/168221350000000), (-74953470358369724091923174072022301843/67992305234455279513137951000000000000)]
    bernstein := [(77303190023066058304527199115702316699557/679923052344552795131379510000000000000000), (6946683853753270920692247621183350314713/60437604652849137345011512000000000000000), (151543280099841449876051508039744016156859/1305452260501541366652248659200000000000000), (906113302454034016683842812609483434369/7736013395564689580161473536000000000000), (1315307490358548051929362201746984108533/11139859289613152995432521891840000000000)]
    reserve := (113694027223/1000000000000) }

theorem quarter_035_019_valid : quarter_035_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_035_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_035_019]
  · intro i; fin_cases i <;> norm_num [quarter_035_019]
  · norm_num [quarter_035_019]
  · norm_num [quarter_035_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_035_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_035_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_035_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_035_019]

def quarter_035_020 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 2, 0, 2, 0, 0, 3]
    lambda := ![(1867317/25000000), (3206487/25000000), (3206487/25000000), (20188449/100000000), (20188449/100000000), (20188449/100000000), (6313489/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (69211/1000000), 0, 0]] i.1) i.2
    mu := ![(73983/12500000), (3324751/100000000), (1/100000000), (6043641/100000000), (1/100000000), (1/100000000), (69211/1000000)]
    alternative := .zero
    polynomial := [(5446928239438946439054380247322387/68592019112971092788322000000000000), (68891000349271/166237550000000), (-30676212624213019486749037766092613/34296009556485546394161000000000000), (68891000349271/166237550000000), (-66799353487864985412552455779507613/68592019112971092788322000000000000)]
    bernstein := [(101841488870780076511404369730209031/864470493189937218649128960000000000), (1286702686498085734071474491637403081/10805881164874215233114112000000000000), (90497557697665474246560162513591475543/752552438268025703734732800000000000000), (532700927648301581101362993720529924129/4389889223230149938452608000000000000000), (1342788940196341927457204267423964589747/10974723058075374846131520000000000000000)]
    reserve := (58903970507/500000000000) }

theorem quarter_035_020_valid : quarter_035_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_035_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_035_020]
  · intro i; fin_cases i <;> norm_num [quarter_035_020]
  · norm_num [quarter_035_020]
  · norm_num [quarter_035_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_035_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_035_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_035_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_035_020]

def quarter_035_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 3]
    lambda := ![(7777781/100000000), (3227599/25000000), (3227599/25000000), (2000893/10000000), (2000893/10000000), (2000893/10000000), (1593659/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3445093/50000000), 0, 0]] i.1) i.2
    mu := ![(354247/50000000), (1638769/50000000), (1/100000000), (1203389/20000000), (1/100000000), (1/100000000), (6890187/100000000)]
    alternative := .zero
    polynomial := [(2954196931208979281439940537613437/39780990915581906988369000000000000), (3231828549173/7448950000000), (-16101086873768337597524649895956563/19890495457790953494184500000000000), (3231828549173/7448950000000), (-35156370678745654476489240329526563/39780990915581906988369000000000000)]
    bernstein := [(777444772200175016951189712315923414797/6364958546493105118139040000000000000000), (1571468104994898884865786466283399836793/12729917092986210236278080000000000000000), (9522443694070012539296956781343422621551/76379502557917261417668480000000000000000), (6406809134317889002852323687158056240273/50919668371944840945112320000000000000000), (12922751370246297007274590281290759563837/101839336743889681890224640000000000000000)]
    reserve := (61072257307/500000000000) }

theorem quarter_035_021_valid : quarter_035_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_035_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_035_021]
  · intro i; fin_cases i <;> norm_num [quarter_035_021]
  · norm_num [quarter_035_021]
  · norm_num [quarter_035_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_035_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_035_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_035_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_035_021]

def quarter_035_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 2, 0, 2, 0, 0, 3]
    lambda := ![0, (1928437/12500000), (1928437/12500000), (1440521/6250000), (1440521/6250000), (1440521/6250000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (9765407/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (752397/12500000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (232699/6250000), (1/100000000), (3504047/50000000), (1/100000000), (1/100000000), (6019177/100000000)]
    alternative := .zero
    polynomial := [(19582360172107149920797955069089/314109830224603006784000000000000), (18831972178859/46539800000000), (-32054474503781719639336869738911/157054915112301503392000000000000), (18831972178859/46539800000000), (-83691309179670589199471694546911/314109830224603006784000000000000)]
    bernstein := [(103589351819827458787429702290757861889/804121165374983697367040000000000000000), (13177763718773079193327996710081358527/100515145671872962170880000000000000000), (1256853109974351448999687705533489727/9423294906738090203520000000000000000), (106521585844547093727756346642562499/785274575561507516960000000000000000), (6768959155395437606782646702572041/49079660972594219810000000000000000)]
    reserve := (128823063339/1000000000000) }

theorem quarter_035_022_valid : quarter_035_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_035_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_035_022]
  · intro i; fin_cases i <;> norm_num [quarter_035_022]
  · norm_num [quarter_035_022]
  · norm_num [quarter_035_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_035_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_035_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_035_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_035_022]

def quarter_035_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 3]
    lambda := ![0, (3166689/20000000), (3166689/20000000), (22777703/100000000), (22777703/100000000), (22777703/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (212557/2000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5948499/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (747789/20000000), (1/100000000), (54761/781250), (1/100000000), (1/100000000), (11897/200000)]
    alternative := .zero
    polynomial := [(60298835442067421670407777/1113550319508144000000000000), (224367304591/498526000000), (-128543692064857867402992223/556775159754072000000000000), (224367304591/498526000000), (-317386219571783156476392223/1113550319508144000000000000)]
    bernstein := [(24023445488482115310724714313/173992237423147500000000000000), (391380043639312556869639830109/2783875798770360000000000000000), (4780517762073871954047029778959/33406509585244320000000000000000), (51886957060565695016686626685633/356336102242606080000000000000000), (422249742233393483965867355543297/2850688817940848640000000000000000)]
    reserve := (27614387681/200000000000) }

theorem quarter_035_023_valid : quarter_035_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_035_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_035_023]
  · intro i; fin_cases i <;> norm_num [quarter_035_023]
  · norm_num [quarter_035_023]
  · norm_num [quarter_035_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_035_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_035_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_035_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_035_023]

def quarter_035_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 2, 0, 2, 0, 0, 3]
    lambda := ![0, (1624867/10000000), (1624867/10000000), (22500887/100000000), (22500887/100000000), (22500887/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (5748411/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5876207/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1872307/50000000), (1/100000000), (7012993/100000000), (1/100000000), (1/100000000), (367263/6250000)]
    alternative := .zero
    polynomial := [(316588283410475888988486493/7133636042748569250000000000), (9340403336337/18723070000000), (-465750931742350150732621441/1783409010687142312500000000), (9340403336337/18723070000000), (-2179592010379876491918972257/7133636042748569250000000000)]
    bernstein := [(2708343670857486450218428393087423/18262108269436337280000000000000000), (21222532242977887459040760692779/140477755918741056000000000000000), (1960103680726522261716721431799/12741005769374188800000000000000), (12941257441443374699472065659/82633974069847680000000000000), (17120887293452096659857511631/107424166290801984000000000000)]
    reserve := (148303998141/1000000000000) }

theorem quarter_035_024_valid : quarter_035_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_035_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_035_024]
  · intro i; fin_cases i <;> norm_num [quarter_035_024]
  · norm_num [quarter_035_024]
  · norm_num [quarter_035_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_035_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_035_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_035_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_035_024]

def quarter_035_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 3]
    lambda := ![0, (16671873/100000000), (16671873/100000000), (22218751/100000000), (22218751/100000000), (22218751/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (1236887/10000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2901263/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3739711/100000000), (1/100000000), (7018977/100000000), (1/100000000), (1/100000000), (5802527/100000000)]
    alternative := .zero
    polynomial := [(294389180973060658990893905327/8959424409412947057000000000000), (20621222979351/37397110000000), (-1322823077884143005411193047173/4479712204706473528500000000000), (20621222979351/37397110000000), (-2940035336741346669813279999673/8959424409412947057000000000000)]
    bernstein := [(21531535525047957554330517285559/134918391106453790976000000000000), (1243374072838270578153723556696863/7645375496032381488640000000000000), (113996158673837080713009017362530653/688083794642914333977600000000000000), (128987675136799126317369341848777719/764537549603238148864000000000000000), (3939414176414236427744342477884522007/22936126488097144465920000000000000000)]
    reserve := (159589329137/1000000000000) }

theorem quarter_035_025_valid : quarter_035_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_035_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_035_025]
  · intro i; fin_cases i <;> norm_num [quarter_035_025]
  · norm_num [quarter_035_025]
  · norm_num [quarter_035_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_035_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_035_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_035_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_035_025]

def quarter_035_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 2, 0, 2, 0, 0, 3]
    lambda := ![0, (17101819/100000000), (17101819/100000000), (21932121/100000000), (21932121/100000000), (21932121/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (3310121/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5727671/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3723869/100000000), (1/100000000), (3513729/50000000), (1/100000000), (1/100000000), (715959/12500000)]
    alternative := .zero
    polynomial := [(60550174620478887956393370971/3122694913628106153000000000000), (56609090210099/93096725000000), (-520957687469161756500036362029/1561347456814053076500000000000), (56609090210099/93096725000000), (-1102465549558802400956466095029/3122694913628106153000000000000)]
    bernstein := [(1375006712111167627277859149815611611/7994098978887951751680000000000000000), (350411024947919627291390421314754403/1998524744721987937920000000000000000), (267803996824696926052485473914920557/1498893558541490953440000000000000000), (22733519107847707375521064972116287/124907796545124246120000000000000000), (5787584288315266816546266024760451/31226949136281061530000000000000000)]
    reserve := (21500339121/125000000000) }

theorem quarter_035_026_valid : quarter_035_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_035_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_035_026]
  · intro i; fin_cases i <;> norm_num [quarter_035_026]
  · norm_num [quarter_035_026]
  · norm_num [quarter_035_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_035_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_035_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_035_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_035_026]

def quarter_035_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 2, 0, 2, 0, 0, 3]
    lambda := ![0, (3507467/20000000), (3507467/20000000), (21641777/100000000), (21641777/100000000), (21641777/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (3527039/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5651847/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3696833/100000000), (1/100000000), (7038509/100000000), (1/100000000), (1/100000000), (5651847/100000000)]
    alternative := .zero
    polynomial := [(276154705889080683243968898739/73531073013769359229500000000000), (12370972900213/18484165000000), (-13849546966018952829060900423761/36765536506884679614750000000000), (12370972900213/18484165000000), (-27975248637926986341365769746261/73531073013769359229500000000000)]
    bernstein := [(136491055125627201125603283948173059/735310730137693592295000000000000000), (556678975268015641704778240700664889/2941242920550774369180000000000000000), (234786173583294603162550705012883633/1217066036089975601040000000000000000), (1321438850885498446655971386683739107/6722840961258912843840000000000000000), (185653506379710527841892554775817393/927288408449505219840000000000000000)]
    reserve := (92811820589/500000000000) }

theorem quarter_035_027_valid : quarter_035_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_035_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_035_027]
  · intro i; fin_cases i <;> norm_num [quarter_035_027]
  · norm_num [quarter_035_027]
  · norm_num [quarter_035_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_035_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_035_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_035_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_035_027]

def quarter_035_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 2, 0, 2, 0, 0, 3]
    lambda := ![0, (17977319/100000000), (17977319/100000000), (10674227/50000000), (10674227/50000000), (10674227/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2993689/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1393811/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3658457/100000000), (1/100000000), (3526087/50000000), (1/100000000), (1/100000000), (1115049/20000000)]
    alternative := .zero
    polynomial := [(-164540975715895772112409301239/11507339281117604152800000000000), (53818502139791/73169140000000), (-2444853489003398199706630766239/5753669640558802076400000000000), (53818502139791/73169140000000), (-4725166002290900627300852231239/11507339281117604152800000000000)]
    bernstein := [(5907559523255326852230627277711291721/29458788559661066631168000000000000000), (1004110509949796984293909210605648073/4909798093276844438528000000000000000), (4606398582014293723456146722497958723/22094091419745799973376000000000000000), (260799495234460405026760363038985633/1227449523319211109632000000000000000), (398540679797977973427649221733186361/1841174284978816664448000000000000000)]
    reserve := (25067050497/125000000000) }

theorem quarter_035_028_valid : quarter_035_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_035_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_035_028]
  · intro i; fin_cases i <;> norm_num [quarter_035_028]
  · norm_num [quarter_035_028]
  · norm_num [quarter_035_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_035_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_035_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_035_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_035_028]

def quarter_035_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 2, 0, 2, 0, 0, 3]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (85870743/100000000), 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (19590439/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-15187964623384429949/15672351200000000000), (85870743/19590439), (-32577730683384429949/7836175600000000000), (85870743/19590439), (-49967496743384429949/15672351200000000000)]
    bernstein := [(491174581772955537851651/2507576192000000000000000), (212375570386690762474719/1003030476800000000000000), (24881778954383083676659/109421506560000000000000), (38974676531101527083863/160484876288000000000000), (16569617307944372801779/64193950515200000000000)]
    reserve := (7835049373/40000000000) }

theorem quarter_035_029_valid : quarter_035_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_035_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_035_029]
  · intro i; fin_cases i <;> norm_num [quarter_035_029]
  · norm_num [quarter_035_029]
  · norm_num [quarter_035_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_035_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_035_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_035_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_035_029]

def quarterTable035 : OwnerTable where
  mode := .quarter
  owners := ![0, 2, 0, 2, 0, 0, 3]
  rows := [quarter_035_000, quarter_035_001, quarter_035_002, quarter_035_003, quarter_035_004, quarter_035_005, quarter_035_006, quarter_035_007, quarter_035_008, quarter_035_009, quarter_035_010, quarter_035_011, quarter_035_012, quarter_035_013, quarter_035_014, quarter_035_015, quarter_035_016, quarter_035_017, quarter_035_018, quarter_035_019, quarter_035_020, quarter_035_021, quarter_035_022, quarter_035_023, quarter_035_024, quarter_035_025, quarter_035_026, quarter_035_027, quarter_035_028, quarter_035_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_035_000_valid
    · exact quarter_035_001_valid
    · exact quarter_035_002_valid
    · exact quarter_035_003_valid
    · exact quarter_035_004_valid
    · exact quarter_035_005_valid
    · exact quarter_035_006_valid
    · exact quarter_035_007_valid
    · exact quarter_035_008_valid
    · exact quarter_035_009_valid
    · exact quarter_035_010_valid
    · exact quarter_035_011_valid
    · exact quarter_035_012_valid
    · exact quarter_035_013_valid
    · exact quarter_035_014_valid
    · exact quarter_035_015_valid
    · exact quarter_035_016_valid
    · exact quarter_035_017_valid
    · exact quarter_035_018_valid
    · exact quarter_035_019_valid
    · exact quarter_035_020_valid
    · exact quarter_035_021_valid
    · exact quarter_035_022_valid
    · exact quarter_035_023_valid
    · exact quarter_035_024_valid
    · exact quarter_035_025_valid
    · exact quarter_035_026_valid
    · exact quarter_035_027_valid
    · exact quarter_035_028_valid
    · exact quarter_035_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
