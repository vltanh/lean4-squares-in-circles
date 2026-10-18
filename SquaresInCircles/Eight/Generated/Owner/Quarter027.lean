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

def quarter_027_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 2, 0, 0, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(102465129/100000000), 0, (19192791/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(560543/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-9336687063886503438164777/457463486508250000000000), (-64079547/560543), (-40663458022347003438164777/228731743254125000000000), (-64079547/560543), (-71990228980807503438164777/457463486508250000000000)]
    bernstein := [(703685342559292178019903367/1873770440737792000000000000), (1875854259774222321528801499/4684426101844480000000000000), (14277826683957307031840585677/35133195763833600000000000000), (11531305198752544833786737987/29277663136528000000000000000), (26588901590914354362542792023/73194157841320000000000000000)]
    reserve := (36326535307/100000000000) }

theorem quarter_027_000_valid : quarter_027_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_027_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_027_000]
  · intro i; fin_cases i <;> norm_num [quarter_027_000]
  · norm_num [quarter_027_000]
  · norm_num [quarter_027_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_027_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_027_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_027_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_027_000]

def quarter_027_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(100371721/100000000), 0, (19887081/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(71153/12500000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-8208487042318949692827207/464548117886000000000000), (-60597559/569224), (-40668488900274449692827207/232274058943000000000000), (-60597559/569224), (-73128490758229949692827207/464548117886000000000000)]
    bernstein := [(25542887225243746976342241593/74327698861760000000000000000), (54783549554092372087240394787/148655397723520000000000000000), (111418677708706730449600452033/297310795447040000000000000000), (215717198152734591859305697947/594621590894080000000000000000), (396003581849212929304558675273/1189243181788160000000000000000)]
    reserve := (83246973351/250000000000) }

theorem quarter_027_001_valid : quarter_027_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_027_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_027_001]
  · intro i; fin_cases i <;> norm_num [quarter_027_001]
  · norm_num [quarter_027_001]
  · norm_num [quarter_027_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_027_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_027_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_027_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_027_001]

def quarter_027_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 2, 0, 0, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(19608541/20000000), 0, (41103203/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(577517/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-1426099006298046362438957/94263219891350000000000), (-56939502/577517), (-8135027509922696362438957/47131609945675000000000), (-56939502/577517), (-14843956013547346362438957/94263219891350000000000)]
    bernstein := [(74943659209813187891663083523/241313842921856000000000000000), (20236252696962981297167944413/60328460730464000000000000000), (15471642832850517916961408309/45246345547848000000000000000), (1246171032223673960933468593/3770528795654000000000000000), (284174818686034867862751883/942632198913500000000000000)]
    reserve := (301469458621/1000000000000) }

theorem quarter_027_002_valid : quarter_027_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_027_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_027_002]
  · intro i; fin_cases i <;> norm_num [quarter_027_002]
  · norm_num [quarter_027_002]
  · norm_num [quarter_027_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_027_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_027_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_027_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_027_002]

def quarter_027_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(47737769/50000000), 0, (84730841/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(585377/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-9773973405635598256572169/764369130194800000000000), (-106220235/1170754), (-65093570208929798256572169/382184565097400000000000), (-106220235/1170754), (-120413167012223998256572169/764369130194800000000000)]
    bernstein := [(2111975726260626713666060111/7643691301948000000000000000), (9208591601509896784563339707/30574765207792000000000000000), (37663862899051992598321534059/122299060831168000000000000000), (145308269583885004690215666383/489196243324672000000000000000), (525814725929969699756030396871/1956784973298688000000000000000)]
    reserve := (16794599723/62500000000) }

theorem quarter_027_003_valid : quarter_027_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_027_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_027_003]
  · intro i; fin_cases i <;> norm_num [quarter_027_003]
  · norm_num [quarter_027_003]
  · norm_num [quarter_027_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_027_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_027_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_027_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_027_003]

def quarter_027_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 2, 0, 0, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(231673/250000), 0, (21776787/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(592757/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-8238678976211038309129793/774005730506800000000000), (-49115626/592757), (-65109733826768638309129793/387002865253400000000000), (-49115626/592757), (-121980788677326238309129793/774005730506800000000000)]
    bernstein := [(477272706590133896248704771087/1981454670097408000000000000000), (52661339155095844167884088237/198145467009740800000000000000), (16217359561567344995261091973/59443640102922240000000000000), (519868938481048435359691749/1981454670097408000000000000), (46506272043574728661489823/198145467009740800000000000)]
    reserve := (9388309053/40000000000) }

theorem quarter_027_004_valid : quarter_027_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_027_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_027_004]
  · intro i; fin_cases i <;> norm_num [quarter_027_004]
  · norm_num [quarter_027_004]
  · norm_num [quarter_027_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_027_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_027_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_027_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_027_004]

def quarter_027_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(22406079/25000000), 0, (44660553/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(299807/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-17030661182269892909521343/1957398529634000000000000), (-44963763/599614), (-162821954872612892909521343/978699264817000000000000), (-44963763/599614), (-308613248562955892909521343/1957398529634000000000000)]
    bernstein := [(102349856194342949148331873/501094023586304000000000000), (1148422154004984670945181561/5010940235863040000000000000), (826745766726247431323963401/3496004815718400000000000000), (113485721831883046226991188473/501094023586304000000000000000), (999296720257540176098060282977/5010940235863040000000000000000)]
    reserve := (99711498563/500000000000) }

theorem quarter_027_005_valid : quarter_027_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_027_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_027_005]
  · intro i; fin_cases i <;> norm_num [quarter_027_005]
  · norm_num [quarter_027_005]
  · norm_num [quarter_027_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_027_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_027_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_027_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_027_005]

def quarter_027_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 2, 0, 0, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(345373/400000), 0, (22839737/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(37869/6250000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-1719924153567237495332851/247241475078000000000000), (-847162/12623), (-20359610527228987495332851/123620737539000000000000), (-847162/12623), (-12999765633630245831777617/82413825026000000000000)]
    bernstein := [(8102730097404880342365201953/48687552015360000000000000000), (15141896346211681502204791021/79117272024960000000000000000), (113495363872629455994497791/570557250180000000000000000), (39006384597562700060214611/206034562565000000000000000), (483828052294162560672937/2971652344687500000000000)]
    reserve := (40703621771/250000000000) }

theorem quarter_027_006_valid : quarter_027_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_027_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_027_006]
  · intro i; fin_cases i <;> norm_num [quarter_027_006]
  · norm_num [quarter_027_006]
  · norm_num [quarter_027_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_027_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_027_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_027_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_027_006]

def quarter_027_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(82830189/100000000), 0, (93207547/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(611587/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-2160864767049455192679741/399296712399400000000000), (-72452831/1223174), (-32587825353125155192679741/199648356199700000000000), (-72452831/1223174), (-63014785939200855192679741/399296712399400000000000)]
    bernstein := [(7944486300681222437123771/62390111312406250000000000), (152061772474782676498816969/998241780998500000000000000), (1917553159418961854195085037/11978901371982000000000000000), (19273738542380305840119167837/127774947967808000000000000000), (127591957454070811210055593059/1022199583742464000000000000000)]
    reserve := (15602622947/125000000000) }

theorem quarter_027_007_valid : quarter_027_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_027_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_027_007]
  · intro i; fin_cases i <;> norm_num [quarter_027_007]
  · norm_num [quarter_027_007]
  · norm_num [quarter_027_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_027_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_027_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_027_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_027_007]

def quarter_027_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 2, 0, 0, 0, 0, 3]
    lambda := ![(2969193/50000000), (11541443/50000000), (11541443/50000000), (11541443/50000000), (4638111/50000000), (4638111/50000000), (6260513/100000000)]
    cone := fun i => (![![(1982321/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (253593/6250000), 0, 0]] i.1) i.2
    mu := ![(9651/25000000), (3248647/50000000), (1/100000000), (1/100000000), (1257187/20000000), (1/100000000), (253593/6250000)]
    alternative := .zero
    polynomial := [(-1855801890187369880173168930918159/13327562209667194242036000000000000), (-1738427847950461879/501643075152000000), (-69107318479183724186020952084188159/6663781104833597121018000000000000), (-1738427847950461879/501643075152000000), (-136358835068180078491868735237458159/13327562209667194242036000000000000)]
    bernstein := [(5410830793570910686953245124335762589041/34118559256748017259612160000000000000000), (2712365151916355969269062708134982809189/17059279628374008629806080000000000000000), (27189045642521320921497045729403546207/171737714379604113722880000000000000000), (667725466813033960467690447979610497549/4264819907093502157451520000000000000000), (327864162191033817728898781119210704321/2132409953546751078725760000000000000000)]
    reserve := (153752875541/1000000000000) }

theorem quarter_027_008_valid : quarter_027_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_027_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_027_008]
  · intro i; fin_cases i <;> norm_num [quarter_027_008]
  · norm_num [quarter_027_008]
  · norm_num [quarter_027_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_027_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_027_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_027_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_027_008]

def quarter_027_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 2, 0, 0, 0, 0, 3]
    lambda := ![(6576867/100000000), (2269441/10000000), (2269441/10000000), (2269441/10000000), (9254779/100000000), (9254779/100000000), (6830347/100000000)]
    cone := fun i => (![![(460873/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2100351/50000000), 0, 0]] i.1) i.2
    mu := ![(2651/6250000), (6421631/100000000), (1/100000000), (1/100000000), (3096457/50000000), (1/100000000), (4200703/100000000)]
    alternative := .zero
    polynomial := [(-1373150701508134951860913128876079/17033298303861696984127000000000000), (-21722814299115688261/6809497512400000000), (-190875161663179238892205999171260283/17033298303861696984127000000000000), (-21722814299115688261/6809497512400000000), (-47375502740417775985086271510596051/4258324575965424246031750000000000)]
    bernstein := [(102809567708788720984285235811066167669/681331932154467879365080000000000000000), (10326344969775850681482075054808725277/68133193215446787936508000000000000000), (1008169532800099666241673326405442523/6674271988451930246841600000000000000), (25053640273794437431790625303327703/167712475607253631843712000000000000), (462695492216111923466756389044961/3156940717313009540587520000000000)]
    reserve := (1145035291/7812500000) }

theorem quarter_027_009_valid : quarter_027_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_027_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_027_009]
  · intro i; fin_cases i <;> norm_num [quarter_027_009]
  · norm_num [quarter_027_009]
  · norm_num [quarter_027_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_027_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_027_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_027_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_027_009]

def quarter_027_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 2, 0, 0, 0, 0, 3]
    lambda := ![(7169673/100000000), (4465321/20000000), (4465321/20000000), (4465321/20000000), (1849703/20000000), (1849703/20000000), (3676741/50000000)]
    cone := fun i => (![![(326771/20000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2167843/50000000), 0, 0]] i.1) i.2
    mu := ![(11483/25000000), (6335607/100000000), (1/100000000), (1/100000000), (6106353/100000000), (1/100000000), (2167843/50000000)]
    alternative := .zero
    polynomial := [(-53265148061411044892086909079/2283060442313777214000000000000), (-2725371978326893101/970023669080000000), (-13665804917862553236973485094079/1141530221156888607000000000000), (-2725371978326893101/970023669080000000), (-27278344687663695429054883279079/2283060442313777214000000000000)]
    bernstein := [(41780874737953199064440406941602571/291390109214708932559831040000000000), (87593342416500331383390842376397109/607062727530643609499648000000000000), (4915235426995552496275776990687485333/34147278423598703034355200000000000000), (675131681905068017556404786564845693/4742677558833153199216000000000000000), (2481524108605463697254208855212179259/17785040845624324497060000000000000000)]
    reserve := (139528726987/1000000000000) }

theorem quarter_027_010_valid : quarter_027_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_027_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_027_010]
  · intro i; fin_cases i <;> norm_num [quarter_027_010]
  · norm_num [quarter_027_010]
  · norm_num [quarter_027_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_027_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_027_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_027_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_027_010]

def quarter_027_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 3]
    lambda := ![(1543507/20000000), (10988699/50000000), (10988699/50000000), (10988699/50000000), (370273/4000000), (370273/4000000), (3918311/50000000)]
    cone := fun i => (![![(1360989/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (446403/10000000), 0, 0]] i.1) i.2
    mu := ![(24589/50000000), (6239401/100000000), (1/100000000), (1/100000000), (3012871/50000000), (1/100000000), (4464031/100000000)]
    alternative := .zero
    polynomial := [(748560587188688600312824410067827/26625011356063740867847600000000000), (-5120905827619349979/2191723302700000000), (-168820931507247505054365100850050173/13312505678031870433923800000000000), (-5120905827619349979/2191723302700000000), (-338390423601683698709043026110168173/26625011356063740867847600000000000)]
    bernstein := [(36213778540334479666511083053608587227/266250113560637408678476000000000000000), (11235143621035419723370397705668280337/81923111864811510362608000000000000000), (583379768448984577905622975758584512143/4260001816970198538855616000000000000000), (177514792093062062223323011878135948933/1310769789836984165801728000000000000000), (9038111258311037824562518057542292675587/68160029071523176621689856000000000000000)]
    reserve := (33150335253/250000000000) }

theorem quarter_027_011_valid : quarter_027_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_027_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_027_011]
  · intro i; fin_cases i <;> norm_num [quarter_027_011]
  · norm_num [quarter_027_011]
  · norm_num [quarter_027_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_027_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_027_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_027_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_027_011]

def quarter_027_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 2, 0, 0, 0, 0, 3]
    lambda := ![(4110551/50000000), (21644963/100000000), (21644963/100000000), (21644963/100000000), (4639607/50000000), (4639607/50000000), (8285581/100000000)]
    cone := fun i => (![![(257917/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (36697/800000), 0, 0]] i.1) i.2
    mu := ![(52173/100000000), (766661/12500000), (1/100000000), (1/100000000), (1190129/20000000), (1/100000000), (36697/800000)]
    alternative := .zero
    polynomial := [(7879350983144198136144102401773/112704714352885323438000000000000), (-16714263329943983/9383930640000000), (-83582991670157638381935124599803/6261373019604740191000000000000), (-16714263329943983/9383930640000000), (-1512373201045981689010976345198227/112704714352885323438000000000000)]
    bernstein := [(2184926546869893266758648085104228589/16972004043728613411840000000000000000), (18764625496388423017288383118193988871/144262034371693214000640000000000000000), (3125998805358268903634487837601810919/24043672395282202333440000000000000000), (4636810622737310513201253260655186319/36065508592923303500160000000000000000), (2267360390182295498904876034754400173/18032754296461651750080000000000000000)]
    reserve := (15716958381/125000000000) }

theorem quarter_027_012_valid : quarter_027_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_027_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_027_012]
  · intro i; fin_cases i <;> norm_num [quarter_027_012]
  · norm_num [quarter_027_012]
  · norm_num [quarter_027_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_027_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_027_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_027_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_027_012]

def quarter_027_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 3]
    lambda := ![(8680991/100000000), (2132767/10000000), (2132767/10000000), (2132767/10000000), (9315279/100000000), (9315279/100000000), (8705441/100000000)]
    cone := fun i => (![![(651991/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (294137/6250000), 0, 0]] i.1) i.2
    mu := ![(54937/100000000), (1504409/25000000), (1/100000000), (1/100000000), (1470171/25000000), (1/100000000), (294137/6250000)]
    alternative := .zero
    polynomial := [(7062763141547002618400220699616741/71478983650111474658982000000000000), (-19042726337123851353/16529543446600000000), (-499817856543462015518635968929113259/35739491825055737329491000000000000), (-19042726337123851353/16529543446600000000), (-1006698476228471033655672158557843259/71478983650111474658982000000000000)]
    bernstein := [(3465342437024938396597797529035053141/28520292728224029789120000000000000000), (938069902727225692245345167061962038647/7624424922678557296958080000000000000000), (16894811856655003049669742972578258143423/137239648608214031345245440000000000000000), (3712173572555984457910242243625651555047/30497699690714229187832320000000000000000), (21753737775489035824435881485890469087941/182986198144285375126993920000000000000000)]
    reserve := (23776370017/200000000000) }

theorem quarter_027_013_valid : quarter_027_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_027_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_027_013]
  · intro i; fin_cases i <;> norm_num [quarter_027_013]
  · norm_num [quarter_027_013]
  · norm_num [quarter_027_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_027_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_027_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_027_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_027_013]

def quarter_027_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 2, 0, 0, 0, 0, 3]
    lambda := ![(9097823/100000000), (5256009/25000000), (5256009/25000000), (5256009/25000000), (9364701/100000000), (9364701/100000000), (4550333/50000000)]
    cone := fun i => (![![(227481/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4822313/100000000), 0, 0]] i.1) i.2
    mu := ![(11497/20000000), (184153/3125000), (1/100000000), (1/100000000), (2907763/50000000), (1/100000000), (2411157/50000000)]
    alternative := .zero
    polynomial := [(13298498407793999816596142612075413/118751146857997482563448000000000000), (-3862057924827705189/8468828164000000000), (-866860397356035828999648734282916587/59375573428998741281724000000000000), (-3862057924827705189/8468828164000000000), (-1747019293119865657815893611177908587/118751146857997482563448000000000000)]
    bernstein := [(34736499627294215606759979822907098213013/304002935956473555362426880000000000000000), (44071411496243215744119397718789955901/380003669945591944203033600000000000000), (66215192416807827807898450337698945813/570005504918387916304550400000000000000), (27273926077411471407616579918738301/237502293715994965126896000000000000), (13298498407793999816596142612075413/118751146857997482563448000000000000)]
    reserve := (111986273477/1000000000000) }

theorem quarter_027_014_valid : quarter_027_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_027_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_027_014]
  · intro i; fin_cases i <;> norm_num [quarter_027_014]
  · norm_num [quarter_027_014]
  · norm_num [quarter_027_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_027_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_027_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_027_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_027_014]

def quarter_027_015 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 3]
    lambda := ![(1886583/20000000), (1294539/6250000), (1294539/6250000), (1294539/6250000), (4624161/50000000), (4624161/50000000), (9932569/100000000)]
    cone := fun i => (![![0, 0, (496551/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (626147/12500000), 0, 0]] i.1) i.2
    mu := ![(3137/5000000), (5750859/100000000), (1/100000000), (1/100000000), (1432921/25000000), (1/100000000), (626147/12500000)]
    alternative := .zero
    polynomial := [(2271005246529962019105685242004359/21581644110000660596428000000000000), (22404921498033505927/24053926244000000000), (-171827103440691938721758199721609641/10790822055000330298214000000000000), (22404921498033505927/24053926244000000000), (-345925212127913839462622084685223641/21581644110000660596428000000000000)]
    bernstein := [(2271005246529962019105685242004359/21581644110000660596428000000000000), (9586574121497980724179105375236161/86326576440002642385712000000000000), (3978375201603548035866935179741417853/34530630576001056954284800000000000000), (16259882766979404009267658268998557761/138122522304004227817139200000000000000), (6550920886478985241654168423868808925159/55249008921601691126855680000000000000000)]
    reserve := (105228556033/1000000000000) }

theorem quarter_027_015_valid : quarter_027_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_027_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_027_015]
  · intro i; fin_cases i <;> norm_num [quarter_027_015]
  · norm_num [quarter_027_015]
  · norm_num [quarter_027_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_027_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_027_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_027_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_027_015]

def quarter_027_016 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 2, 0, 0, 0, 0, 3]
    lambda := ![(4949317/50000000), (20790257/100000000), (20790257/100000000), (20790257/100000000), (142883/1562500), (142883/1562500), (9441571/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4853839/100000000), 0, 0]] i.1) i.2
    mu := ![(134963/50000000), (2852183/50000000), (1/100000000), (1/100000000), (573899/10000000), (1/100000000), (4853839/100000000)]
    alternative := .zero
    polynomial := [(56986579680747120479596398684302107/536145851000434566582884500000000000), (31351149800691/57043660000000), (-982650028501210885868403425922215393/268072925500217283291442250000000000), (31351149800691/57043660000000), (-2022286636683168892216403250528732893/536145851000434566582884500000000000)]
    bernstein := [(161609509328446232932512627973028588929507/1372533378561112490452184320000000000000000), (82379366116849073388995587541027362658907/686266689280556245226092160000000000000000), (125540809607782294090077745708177368447721/1029400033920834367839138240000000000000000), (21187184428142847836535731789346545160507/171566672320139061306523040000000000000000), (10692926384876403066192581721600642572707/85783336160069530653261520000000000000000)]
    reserve := (459943019/3906250000) }

theorem quarter_027_016_valid : quarter_027_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_027_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_027_016]
  · intro i; fin_cases i <;> norm_num [quarter_027_016]
  · norm_num [quarter_027_016]
  · norm_num [quarter_027_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_027_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_027_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_027_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_027_016]

def quarter_027_017 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 3]
    lambda := ![(10300247/100000000), (10366807/50000000), (10366807/50000000), (10366807/50000000), (8988797/100000000), (8988797/100000000), (9521317/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4833999/100000000), 0, 0]] i.1) i.2
    mu := ![(422891/100000000), (5612523/100000000), (1/100000000), (1/100000000), (356883/6250000), (1/100000000), (2417/50000)]
    alternative := .zero
    polynomial := [(282628125872259409227370526453/2785490929590882721800000000000), (4005482083853/7015653750000), (-24673576299943919656862429685829/9749218253568089526300000000000), (4005482083853/7015653750000), (-51325549480993655178316453056829/19498436507136179052600000000000)]
    bernstein := [(128678225243049637550905772947746657/1039916613713929549472000000000000000), (261526753039148990878170538634097171/2079833227427859098944000000000000000), (4772857563670738419720204501041516417/37436998093701463780992000000000000000), (3219033759912420516853988655142797617/24957998729134309187328000000000000000), (928481674925128043610855646248383093/7130856779752659767808000000000000000)]
    reserve := (7733686501/62500000000) }

theorem quarter_027_017_valid : quarter_027_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_027_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_027_017]
  · intro i; fin_cases i <;> norm_num [quarter_027_017]
  · norm_num [quarter_027_017]
  · norm_num [quarter_027_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_027_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_027_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_027_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_027_017]

def quarter_027_018 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 2, 0, 0, 0, 0, 3]
    lambda := ![(10697731/100000000), (2067841/10000000), (2067841/10000000), (2067841/10000000), (884177/10000000), (884177/10000000), (19167/200000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4811841/100000000), 0, 0]] i.1) i.2
    mu := ![(581811/100000000), (5513091/100000000), (1/100000000), (1/100000000), (88791/1562500), (1/100000000), (2405921/50000000)]
    alternative := .zero
    polynomial := [(14625086490715985398965093477008617/152270188505257348154958000000000000), (32688148288471/55130910000000), (-151020649099448664150249511855791383/76135094252628674077479000000000000), (32688148288471/55130910000000), (-316666384689613313699464117188591383/152270188505257348154958000000000000)]
    bernstein := [(50497181427724786860518534721339575787577/389811682573458811276692480000000000000000), (12808162617137840145085589429994557795459/97452920643364702819173120000000000000000), (9729401661824101581781943881010404096759/73089690482523527114379840000000000000000), (2705734810774885028233948763133724217/20101675050198989855440000000000000000), (682893569563621559155398233303423439/5025418762549747463860000000000000000)]
    reserve := (25908500789/200000000000) }

theorem quarter_027_018_valid : quarter_027_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_027_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_027_018]
  · intro i; fin_cases i <;> norm_num [quarter_027_018]
  · norm_num [quarter_027_018]
  · norm_num [quarter_027_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_027_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_027_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_027_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_027_018]

def quarter_027_019 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 2, 0, 0, 0, 0, 3]
    lambda := ![(2218089/20000000), (5156269/25000000), (5156269/25000000), (5156269/25000000), (13599/156250), (13599/156250), (1203451/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2393607/50000000), 0, 0]] i.1) i.2
    mu := ![(372877/50000000), (2703207/50000000), (1/100000000), (1/100000000), (5656547/100000000), (1/100000000), (957443/20000000)]
    alternative := .zero
    polynomial := [(37801067580223446022885681932231601/419919338093352508718463000000000000), (27736911696187/45053450000000), (-349420547126759217960132889273748399/209959669046676254359231500000000000), (27736911696187/45053450000000), (-736642161833741881943151460479728399/419919338093352508718463000000000000)]
    bernstein := [(568496193684285494363352382403636401801/4199193380933525087184630000000000000000), (153658350034956242010718642436374225927/1119784901582273356582568000000000000000), (1119836582016942909257023394042828588887/8062451291392368167394489600000000000000), (20124433190829565683252870018440297951/143332467402530989642568704000000000000), (750158926868803407331578186967786813/5292275719478067309879459840000000000)]
    reserve := (67691118521/500000000000) }

theorem quarter_027_019_valid : quarter_027_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_027_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_027_019]
  · intro i; fin_cases i <;> norm_num [quarter_027_019]
  · norm_num [quarter_027_019]
  · norm_num [quarter_027_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_027_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_027_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_027_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_027_019]

def quarter_027_020 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 2, 0, 0, 0, 0, 3]
    lambda := ![0, (2609333/10000000), (2609333/10000000), (2609333/10000000), (2172001/20000000), (2172001/20000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (14380439/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2836139/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (203943/3125000), (1/100000000), (1/100000000), (1428303/20000000), (1/100000000), (2836139/100000000)]
    alternative := .zero
    polynomial := [(2559819058390696976824978431601/35248884584058339456000000000000), (37523354037187/65261760000000), (-7144462294616452424911989298399/17624442292029169728000000000000), (37523354037187/65261760000000), (-5616247882541200608882985676133/11749628194686113152000000000000)]
    bernstein := [(803699574037563952003341320504569/5775177250252118336471040000000000), (10270412279782189953639662929574519/72189715628151479205888000000000000), (393480598528366924620635419136626523/2707114336055680470220800000000000000), (334798451842576165993896647225723867/2255928613379733725184000000000000000), (854116955935572939340041224676386881/5639821533449334312960000000000000000)]
    reserve := (139164486077/1000000000000) }

theorem quarter_027_020_valid : quarter_027_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_027_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_027_020]
  · intro i; fin_cases i <;> norm_num [quarter_027_020]
  · norm_num [quarter_027_020]
  · norm_num [quarter_027_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_027_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_027_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_027_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_027_020]

def quarter_027_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 3]
    lambda := ![0, (26274061/100000000), (26274061/100000000), (26274061/100000000), (10588909/100000000), (10588909/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (7789159/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2765341/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (807927/12500000), (1/100000000), (1/100000000), (7157811/100000000), (1/100000000), (2765341/100000000)]
    alternative := .zero
    polynomial := [(915411175974612017668249857457/14215054170780910024000000000000), (204652838704699/323170800000000), (-9133524975733661633279484539129/21322581256171365036000000000000), (204652838704699/323170800000000), (-21013283479391159319563718650629/42645162512342730072000000000000)]
    bernstein := [(344884592816804317256267848554443417/2274408667324945603840000000000000000), (2115437137059960204717920999830238719/13646452003949673623040000000000000000), (12967610047640145579963635232473083033/81878712023698041738240000000000000000), (2942425555603985743745436154390763853/18195269338599564830720000000000000000), (18016839870803133141694681545829372571/109171616031597388984320000000000000000)]
    reserve := (151637037693/1000000000000) }

theorem quarter_027_021_valid : quarter_027_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_027_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_027_021]
  · intro i; fin_cases i <;> norm_num [quarter_027_021]
  · norm_num [quarter_027_021]
  · norm_num [quarter_027_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_027_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_027_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_027_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_027_021]

def quarter_027_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 2, 0, 0, 0, 0, 3]
    lambda := ![0, (26461941/100000000), (26461941/100000000), (26461941/100000000), (10307089/100000000), (10307089/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (16750069/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1345871/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (6386173/100000000), (1/100000000), (1/100000000), (3587857/50000000), (1/100000000), (2691743/100000000)]
    alternative := .zero
    polynomial := [(13442993897114095556520530288657/246700135567163151692000000000000), (443239337623929/638617300000000), (-56119273759369032453232138110343/123350067783581575846000000000000), (443239337623929/638617300000000), (-125681541415852160462984806509343/246700135567163151692000000000000)]
    bernstein := [(104370777134064600388963391371946405057/631552347051937668331520000000000000000), (13336304010787171632477330769970382351/78944043381492208541440000000000000000), (1277319959230579793683676151497706701/7401004067014894550760000000000000000), (8360443428241083953363838403928499/47442333762915990710000000000000000), (533258986584040057752526893253541/2965145860182249419375000000000000)]
    reserve := (82630345387/500000000000) }

theorem quarter_027_022_valid : quarter_027_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_027_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_027_022]
  · intro i; fin_cases i <;> norm_num [quarter_027_022]
  · norm_num [quarter_027_022]
  · norm_num [quarter_027_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_027_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_027_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_027_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_027_022]

def quarter_027_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 3]
    lambda := ![0, (13328183/50000000), (13328183/50000000), (13328183/50000000), (10015451/100000000), (10015451/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (1118281/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (130779/5000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (6294693/100000000), (1/100000000), (1/100000000), (1439053/20000000), (1/100000000), (130779/5000000)]
    alternative := .zero
    polynomial := [(1535436335930785518972777521/35898426699624027000000000000), (14904653813423/19670915625000), (-8713785668767971940202018479/17949213349812013500000000000), (14904653813423/19670915625000), (-18963007673466729399376814479/35898426699624027000000000000)]
    bernstein := [(1010256648738051963287895853049/5609129171816254218750000000000), (1501973341081470703394118473687/8158733340823642500000000000000), (28933428931610397583993453748801/153850400141245830000000000000000), (200524849260020365870172212355219/1044317867625426240000000000000000), (18008184608470331024155197430606481/91899972351037509120000000000000000)]
    reserve := (22513669631/125000000000) }

theorem quarter_027_023_valid : quarter_027_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_027_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_027_023]
  · intro i; fin_cases i <;> norm_num [quarter_027_023]
  · norm_num [quarter_027_023]
  · norm_num [quarter_027_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_027_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_027_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_027_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_027_023]

def quarter_027_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 2, 0, 0, 0, 0, 3]
    lambda := ![0, (13428361/50000000), (13428361/50000000), (13428361/50000000), (4857459/50000000), (4857459/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (19002599/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1268547/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (6189309/100000000), (1/100000000), (1/100000000), (1443299/20000000), (1/100000000), (507419/20000000)]
    alternative := .zero
    polynomial := [(47942566914702295399002763517/1648285762352985756000000000000), (36453394187177/44209350000000), (-142903614766981243118883498161/274714293725497626000000000000), (36453394187177/44209350000000), (-905364255516589754112303752483/1648285762352985756000000000000)]
    bernstein := [(828153331419580783602167604716685437/4219611551623643535360000000000000000), (6510526018973119685999814188109001/32458550397104950272000000000000000), (8645260940061417736659941455442461/42196115516236435353600000000000000), (67894762224207057488081719325257/324585503971049502720000000000000), (5298178615906484023013330543789/24821244421315550208000000000000)]
    reserve := (98131465573/500000000000) }

theorem quarter_027_024_valid : quarter_027_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_027_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_027_024]
  · intro i; fin_cases i <;> norm_num [quarter_027_024]
  · norm_num [quarter_027_024]
  · norm_num [quarter_027_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_027_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_027_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_027_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_027_024]

def quarter_027_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 3]
    lambda := ![0, (6765597/25000000), (6765597/25000000), (6765597/25000000), (9406417/100000000), (9406417/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (20077599/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (153533/6250000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3035217/50000000), (1/100000000), (1/100000000), (7239419/100000000), (1/100000000), (153533/6250000)]
    alternative := .zero
    polynomial := [(23855860278318622378912312717/1799259992189922644800000000000), (45278981187201/50586950000000), (-503328557537381212944990892883/899629996094961322400000000000), (45278981187201/50586950000000), (-1030512975353081048268894098483/1799259992189922644800000000000)]
    bernstein := [(98481890888041988090574787336813/460610558000620197068800000000000), (1006334029160843587389440814999519/4606105580006201970688000000000000), (30833992494815479858991269853929663/138183167400186059120640000000000000), (104922187042872377113498503097419447/460610558000620197068800000000000000), (1070605160001778228312653270846692797/4606105580006201970688000000000000000)]
    reserve := (213807280743/1000000000000) }

theorem quarter_027_025_valid : quarter_027_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_027_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_027_025]
  · intro i; fin_cases i <;> norm_num [quarter_027_025]
  · norm_num [quarter_027_025]
  · norm_num [quarter_027_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_027_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_027_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_027_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_027_025]

def quarter_027_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 2, 0, 0, 0, 0, 3]
    lambda := ![0, (27272749/100000000), (27272749/100000000), (27272749/100000000), (2272719/25000000), (2272719/25000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (2111497/10000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2374123/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2969279/50000000), (1/100000000), (1/100000000), (3632021/50000000), (1/100000000), (2374123/100000000)]
    alternative := .zero
    polynomial := [(-251706356793168510501322516743/51207381509200515314000000000000), (57586327695253/59385580000000), (-15458764750520534181865375624243/25603690754600257657000000000000), (57586327695253/59385580000000), (-30665823144247899853229428731743/51207381509200515314000000000000)]
    bernstein := [(30522461448890522884056496827645581137/131090896663553319203840000000000000000), (7796079125987803746826448707638488601/32772724165888329800960000000000000000), (5970963866289759052251039173605785719/24579543124416247350720000000000000000), (507892078636320879846040339038425629/2048295260368020612560000000000000000), (129548055901238470257108994154661417/512073815092005153140000000000000000)]
    reserve := (232834332709/1000000000000) }

theorem quarter_027_026_valid : quarter_027_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_027_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_027_026]
  · intro i; fin_cases i <;> norm_num [quarter_027_026]
  · norm_num [quarter_027_026]
  · norm_num [quarter_027_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_027_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_027_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_027_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_027_026]

def quarter_027_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 2, 0, 0, 0, 0, 3]
    lambda := ![0, (27487193/100000000), (27487193/100000000), (27487193/100000000), (876921/10000000), (876921/10000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (22112459/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1145059/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (5794241/100000000), (1/100000000), (1/100000000), (3645177/50000000), (1/100000000), (2290119/100000000)]
    alternative := .zero
    polynomial := [(-42454646831057710018014443843/1653664318694139596000000000000), (607809428237587/579424100000000), (-540367436046299942947187116843/826832159347069798000000000000), (607809428237587/579424100000000), (-1038280225261542175876359789843/1653664318694139596000000000000)]
    bernstein := [(4191080184925187611598930612675317/16536643186941395960000000000000000), (17124936399623141156350755992422607/66146572747765583840000000000000000), (209822614800314258967103112291117291/793758872973187006080000000000000000), (4680719109877358160321783850808767/17349920720725399040000000000000000), (19100398857585182351492669933264257/69399682882901596160000000000000000)]
    reserve := (31680251983/125000000000) }

theorem quarter_027_027_valid : quarter_027_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_027_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_027_027]
  · intro i; fin_cases i <;> norm_num [quarter_027_027]
  · norm_num [quarter_027_027]
  · norm_num [quarter_027_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_027_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_027_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_027_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_027_027]

def quarter_027_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 2, 0, 0, 0, 0, 3]
    lambda := ![0, (173157/625000), (173157/625000), (173157/625000), (8442321/100000000), (8442321/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (11534049/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8819/400000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (5638103/100000000), (1/100000000), (1/100000000), (1829583/25000000), (1/100000000), (8819/400000)]
    alternative := .zero
    polynomial := [(-249109924285680419097453333/5053961849991729500000000000), (1997201322693/1761907187500), (-1792538466410501394617013333/2526980924995864750000000000), (1997201322693/1761907187500), (-3335967008535322370136573333/5053961849991729500000000000)]
    bernstein := [(3567490133556733398381404018069787/12938142335978827520000000000000000), (1821792003923148759858594068565393/6469071167989413760000000000000000), (929911898900759079425242341380227/3234535583994706880000000000000000), (474461852274321373759115448973353/1617267791997353440000000000000000), (241983516313844637453178535493867/808633895998676720000000000000000)]
    reserve := (275734339669/1000000000000) }

theorem quarter_027_028_valid : quarter_027_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_027_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_027_028]
  · intro i; fin_cases i <;> norm_num [quarter_027_028]
  · norm_num [quarter_027_028]
  · norm_num [quarter_027_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_027_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_027_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_027_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_027_028]

def quarter_027_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 2, 0, 0, 0, 0, 3]
    lambda := ![0, (33333333/100000000), (33333333/100000000), (33333333/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (28623581/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9873603/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (6530147/100000000), (1/100000000), (1/100000000), (270777/3125000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-791352488847721368036173/5803367759488000000000000), (954119357125473/653014700000000), (-2937790811621204592324173/2901683879744000000000000), (954119357125473/653014700000000), (-5084229134394687816612173/5803367759488000000000000)]
    bernstein := [(279023570419861849652590111027/928538841518080000000000000000), (114253662594494344577861152463/371415536607232000000000000000), (140271802598845565369771974273/445698643928678400000000000000), (19124525956096234960326270151/59426485857157120000000000000), (7818190784798868847520642083/23770594342862848000000000000)]
    reserve := (300497467573/1000000000000) }

theorem quarter_027_029_valid : quarter_027_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_027_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_027_029]
  · intro i; fin_cases i <;> norm_num [quarter_027_029]
  · norm_num [quarter_027_029]
  · norm_num [quarter_027_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_027_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_027_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_027_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_027_029]

def quarterTable027 : OwnerTable where
  mode := .quarter
  owners := ![0, 2, 0, 0, 0, 0, 3]
  rows := [quarter_027_000, quarter_027_001, quarter_027_002, quarter_027_003, quarter_027_004, quarter_027_005, quarter_027_006, quarter_027_007, quarter_027_008, quarter_027_009, quarter_027_010, quarter_027_011, quarter_027_012, quarter_027_013, quarter_027_014, quarter_027_015, quarter_027_016, quarter_027_017, quarter_027_018, quarter_027_019, quarter_027_020, quarter_027_021, quarter_027_022, quarter_027_023, quarter_027_024, quarter_027_025, quarter_027_026, quarter_027_027, quarter_027_028, quarter_027_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_027_000_valid
    · exact quarter_027_001_valid
    · exact quarter_027_002_valid
    · exact quarter_027_003_valid
    · exact quarter_027_004_valid
    · exact quarter_027_005_valid
    · exact quarter_027_006_valid
    · exact quarter_027_007_valid
    · exact quarter_027_008_valid
    · exact quarter_027_009_valid
    · exact quarter_027_010_valid
    · exact quarter_027_011_valid
    · exact quarter_027_012_valid
    · exact quarter_027_013_valid
    · exact quarter_027_014_valid
    · exact quarter_027_015_valid
    · exact quarter_027_016_valid
    · exact quarter_027_017_valid
    · exact quarter_027_018_valid
    · exact quarter_027_019_valid
    · exact quarter_027_020_valid
    · exact quarter_027_021_valid
    · exact quarter_027_022_valid
    · exact quarter_027_023_valid
    · exact quarter_027_024_valid
    · exact quarter_027_025_valid
    · exact quarter_027_026_valid
    · exact quarter_027_027_valid
    · exact quarter_027_028_valid
    · exact quarter_027_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
