module

public import SquaresInCircles.Eight.Arithmetic.Bernstein

/-! Generated source, schema eight-polynomial-v1. Uncompiled.
Exact polynomial data and full algebraic expansions; no report status is a premise. -/

@[expose] public section
open scoped BigOperators
namespace SquaresInCircles.Eight.Generated

/-- Source: high_high_whole_pair_hand_arithmetic.json, polynomial poly_polynomial. -/
def high_high_whole_pair_poly_polynomial : Arithmetic.BernsteinRow :=
  { interval := ⟨(3/5),(19/20)⟩
    polynomial := [(65061887296399928500418892361/62500000000000000000000000000), (-14361530534617802192848951/6250000000000000000000000), (-395814506222929894934369/1562500000000000000000000), (44764226035050131557357117/12500000000000000000000000), (-3449913973653868140397513/1562500000000000000000000), (-67589710177681104489577917/250000000000000000000000000), (49033978091542260142307551/93750000000000000000000000), (-3845526581737986312557/117187500000000000000000), (-16331055428326233593923/300000000000000000000000), (44376341560401292601/7500000000000000000000), (36010985562250571555267/12000000000000000000000000), (-78301333229349206449/250000000000000000000000), (-50471846334608017259/562500000000000000000000), (4308315637825501/703125000000000000000), (4462364729761/3515625000000000000)]
    degree := 14
    coefficients := [(14669583267672231987689498498329/244140625000000000000000000000000), (88315175302997474908154070223233/1953125000000000000000000000000000), (6640157706331547878852795276151799/203125000000000000000000000000000000), (18209759744242642391807518389125891/812500000000000000000000000000000000), (127610395342535725747327485329273233/8937500000000000000000000000000000000), (1168650970497872164509539280317612589/143000000000000000000000000000000000000), (929157356003981479484371114285357883/234000000000000000000000000000000000000), (3530328250748472641342356968187754037/2288000000000000000000000000000000000000), (6908780946184157841421089297178445633/9152000000000000000000000000000000000000), (161500786839709773398221863591050275753/109824000000000000000000000000000000000000), (141937117010348194054418539048175976191/39936000000000000000000000000000000000000), (45738834710153918915988414060378049859/6656000000000000000000000000000000000000), (52040868965623984587512790805864930289/4608000000000000000000000000000000000000), (2136912010634037898636137059397142679/128000000000000000000000000000000000000), (23507704513769642194328894577210970521/1024000000000000000000000000000000000000)] }

theorem high_high_whole_pair_poly_polynomial_valid : high_high_whole_pair_poly_polynomial.Valid (6908780946184157841421089297178445633/18304000000000000000000000000000000000000) := by
  constructor
  · norm_num [high_high_whole_pair_poly_polynomial]
  · rfl
  · intro t
    norm_num [high_high_whole_pair_poly_polynomial, Arithmetic.QPoly.eval, Arithmetic.bernsteinEval,
      Arithmetic.bernsteinBasis, Arithmetic.BernsteinRow.coefficient,
      Finset.sum_range_succ]
    ring
  · intro i hi
    have hi' : i ≤ 14 := hi
    interval_cases i <;> norm_num [high_high_whole_pair_poly_polynomial,Arithmetic.BernsteinRow.coefficient]

theorem high_high_whole_pair_poly_polynomial_positive {x : ℝ} (hx : ((3/5) : ℝ) ≤ x ∧ x ≤ (19/20)) :
    0 < high_high_whole_pair_poly_polynomial.polynomial.eval x :=
  high_high_whole_pair_poly_polynomial_valid.positive (by norm_num) hx

/-- Source: low_low_whole_pair_hand_arithmetic.json, polynomial plus_circle. -/
def low_low_whole_pair_plus_circle : Arithmetic.BernsteinRow :=
  { interval := ⟨0,(24/25)⟩
    polynomial := [(35133671271797089/640000000000000000), (22151369317/80000000000), (-203822280977/400000000000), (66275381361/160000000000), (-315895906341/1600000000000), (-4131580317/80000000000), (35099399403/4000000000000), (171/160000), (9/640000)]
    degree := 8
    coefficients := [(35133671271797089/640000000000000000), (56398985816117089/640000000000000000), (66930436694814049/640000000000000000), (70916325036731233/640000000000000000), (310676537337644320951/2800000000000000000000), (296876582698131151543/2800000000000000000000), (163393995504564420807367/1750000000000000000000000), (16627399947526384823617/250000000000000000000000), (3866007991357988342593/250000000000000000000000)] }

theorem low_low_whole_pair_plus_circle_valid : low_low_whole_pair_plus_circle.Valid (3866007991357988342593/500000000000000000000000) := by
  constructor
  · norm_num [low_low_whole_pair_plus_circle]
  · rfl
  · intro t
    norm_num [low_low_whole_pair_plus_circle, Arithmetic.QPoly.eval, Arithmetic.bernsteinEval,
      Arithmetic.bernsteinBasis, Arithmetic.BernsteinRow.coefficient,
      Finset.sum_range_succ]
    ring
  · intro i hi
    have hi' : i ≤ 8 := hi
    interval_cases i <;> norm_num [low_low_whole_pair_plus_circle,Arithmetic.BernsteinRow.coefficient]

theorem low_low_whole_pair_plus_circle_positive {x : ℝ} (hx : (0 : ℝ) ≤ x ∧ x ≤ (24/25)) :
    0 < low_low_whole_pair_plus_circle.polynomial.eval x :=
  low_low_whole_pair_plus_circle_valid.positive (by norm_num) hx

/-- Source: low_low_whole_pair_hand_arithmetic.json, polynomial plus_endpoint. -/
def low_low_whole_pair_plus_endpoint : Arithmetic.BernsteinRow :=
  { interval := ⟨(24/25),(11/7)⟩
    polynomial := [(1399093/40000000), (24829/160000), (-27573093/80000000), (45057/320000), (9191031/320000000), (-45057/6400000), (-3063677/3200000000)]
    degree := 6
    coefficients := [(429103148502953/48828125000000000), (9409825857911/2563476562500000), (1018076380061/468750000000000), (26694606981061/4287500000000000), (126755013317599/7203000000000000), (38018165601799/1008420000000000), (25364074522933/376476800000000)] }

theorem low_low_whole_pair_plus_endpoint_valid : low_low_whole_pair_plus_endpoint.Valid (1018076380061/937500000000000) := by
  constructor
  · norm_num [low_low_whole_pair_plus_endpoint]
  · rfl
  · intro t
    norm_num [low_low_whole_pair_plus_endpoint, Arithmetic.QPoly.eval, Arithmetic.bernsteinEval,
      Arithmetic.bernsteinBasis, Arithmetic.BernsteinRow.coefficient,
      Finset.sum_range_succ]
    ring
  · intro i hi
    have hi' : i ≤ 6 := hi
    interval_cases i <;> norm_num [low_low_whole_pair_plus_endpoint,Arithmetic.BernsteinRow.coefficient]

theorem low_low_whole_pair_plus_endpoint_positive {x : ℝ} (hx : ((24/25) : ℝ) ≤ x ∧ x ≤ (11/7)) :
    0 < low_low_whole_pair_plus_endpoint.polynomial.eval x :=
  low_low_whole_pair_plus_endpoint_valid.positive (by norm_num) hx

/-- Source: low_low_whole_pair_hand_arithmetic.json, polynomial minus_circle. -/
def low_low_whole_pair_minus_circle : Arithmetic.BernsteinRow :=
  { interval := ⟨0,(11/10)⟩
    polynomial := [(98758145863541089/640000000000000000), (12195665297/40000000000), (-42763421017/80000000000), (101682691403/240000000000), (-219636578983/960000000000), (-21732753/400000000), (1947578543/180000000000), (91/80000), (9/640000)]
    degree := 8
    coefficients := [(98758145863541089/640000000000000000), (125588609516941089/640000000000000000), (963446033331247623/4480000000000000000), (424027517972242267/1920000000000000000), (420278579498744687/1920000000000000000), (932440532857221523/4480000000000000000), (7268712522339076891/40320000000000000000), (138111881586003377/1152000000000000000), (33137867620677937/5760000000000000000)] }

theorem low_low_whole_pair_minus_circle_valid : low_low_whole_pair_minus_circle.Valid (33137867620677937/11520000000000000000) := by
  constructor
  · norm_num [low_low_whole_pair_minus_circle]
  · rfl
  · intro t
    norm_num [low_low_whole_pair_minus_circle, Arithmetic.QPoly.eval, Arithmetic.bernsteinEval,
      Arithmetic.bernsteinBasis, Arithmetic.BernsteinRow.coefficient,
      Finset.sum_range_succ]
    ring
  · intro i hi
    have hi' : i ≤ 8 := hi
    interval_cases i <;> norm_num [low_low_whole_pair_minus_circle,Arithmetic.BernsteinRow.coefficient]

theorem low_low_whole_pair_minus_circle_positive {x : ℝ} (hx : (0 : ℝ) ≤ x ∧ x ≤ (11/10)) :
    0 < low_low_whole_pair_minus_circle.polynomial.eval x :=
  low_low_whole_pair_minus_circle_valid.positive (by norm_num) hx

/-- Source: low_low_whole_pair_hand_arithmetic.json, polynomial minus_endpoint. -/
def low_low_whole_pair_minus_endpoint : Arithmetic.BernsteinRow :=
  { interval := ⟨(11/10),(11/7)⟩
    polynomial := [(21571/200000), (89/800), (-146937/400000), (237/1600), (48979/1600000), (-237/32000), (-48979/48000000)]
    degree := 6
    coefficients := [(671196625781/48000000000000), (310619959331/33600000000000), (183597014183/23520000000000), (173483469797/16464000000000), (209907793337/11524800000000), (253812062471/8067360000000), (5842180619/115248000000)] }

theorem low_low_whole_pair_minus_endpoint_valid : low_low_whole_pair_minus_endpoint.Valid (183597014183/47040000000000) := by
  constructor
  · norm_num [low_low_whole_pair_minus_endpoint]
  · rfl
  · intro t
    norm_num [low_low_whole_pair_minus_endpoint, Arithmetic.QPoly.eval, Arithmetic.bernsteinEval,
      Arithmetic.bernsteinBasis, Arithmetic.BernsteinRow.coefficient,
      Finset.sum_range_succ]
    ring
  · intro i hi
    have hi' : i ≤ 6 := hi
    interval_cases i <;> norm_num [low_low_whole_pair_minus_endpoint,Arithmetic.BernsteinRow.coefficient]

theorem low_low_whole_pair_minus_endpoint_positive {x : ℝ} (hx : ((11/10) : ℝ) ≤ x ∧ x ≤ (11/7)) :
    0 < low_low_whole_pair_minus_endpoint.polynomial.eval x :=
  low_low_whole_pair_minus_endpoint_valid.positive (by norm_num) hx

/-- Source: low_low_whole_pair_hand_arithmetic.json, polynomial negative_target_axial. -/
def low_low_whole_pair_negative_target_axial : Arithmetic.BernsteinRow :=
  { interval := ⟨0,(11/7)⟩
    polynomial := [(37/1000), (10001/312500), (-39/200), (100833/625000), (13/800), (-100833/12500000), (-13/24000), 0]
    degree := 7
    coefficients := [(37/1000), (1353147/30625000), (3048279/107187500), (57399893/7503125000), (532933781/210087500000), (24240876747/735306250000), (6986562407653/61765725000000), (2165710381999/8823675000000)] }

theorem low_low_whole_pair_negative_target_axial_valid : low_low_whole_pair_negative_target_axial.Valid (532933781/420175000000) := by
  constructor
  · norm_num [low_low_whole_pair_negative_target_axial]
  · rfl
  · intro t
    norm_num [low_low_whole_pair_negative_target_axial, Arithmetic.QPoly.eval, Arithmetic.bernsteinEval,
      Arithmetic.bernsteinBasis, Arithmetic.BernsteinRow.coefficient,
      Finset.sum_range_succ]
    ring
  · intro i hi
    have hi' : i ≤ 7 := hi
    interval_cases i <;> norm_num [low_low_whole_pair_negative_target_axial,Arithmetic.BernsteinRow.coefficient]

theorem low_low_whole_pair_negative_target_axial_positive {x : ℝ} (hx : (0 : ℝ) ≤ x ∧ x ≤ (11/7)) :
    0 < low_low_whole_pair_negative_target_axial.polynomial.eval x :=
  low_low_whole_pair_negative_target_axial_valid.positive (by norm_num) hx

/-- Source: wrong_0011011_edge2_negative_core_corner_arithmetic.json, polynomial poly_tables_5. -/
def wrong_0011011_edge2_negative_core_corner_arithmetic_poly_tables_5 : Arithmetic.BernsteinRow :=
  { interval := ⟨(133/100),(17/10)⟩
    polynomial := [(66556322312577/40000000000000), (3464704398502067/2500000000000000), (2271894991245521/2000000000000000), (4633499234814279/5000000000000000), (1914505862803681/2500000000000000), (8161513540477/12500000000000)]
    degree := 5
    coefficients := [(3202520195857836586374573/250000000000000000000000), (18486681254677277652985161/1250000000000000000000000), (4289084725707616529993421/250000000000000000000000), (124968091633842617159649/6250000000000000000000), (29259987334691313624251/1250000000000000000000), (688056878269900250341/25000000000000000000)] }

theorem wrong_0011011_edge2_negative_core_corner_arithmetic_poly_tables_5_valid : wrong_0011011_edge2_negative_core_corner_arithmetic_poly_tables_5.Valid (3202520195857836586374573/500000000000000000000000) := by
  constructor
  · norm_num [wrong_0011011_edge2_negative_core_corner_arithmetic_poly_tables_5]
  · rfl
  · intro t
    norm_num [wrong_0011011_edge2_negative_core_corner_arithmetic_poly_tables_5, Arithmetic.QPoly.eval, Arithmetic.bernsteinEval,
      Arithmetic.bernsteinBasis, Arithmetic.BernsteinRow.coefficient,
      Finset.sum_range_succ]
    ring
  · intro i hi
    have hi' : i ≤ 5 := hi
    interval_cases i <;> norm_num [wrong_0011011_edge2_negative_core_corner_arithmetic_poly_tables_5,Arithmetic.BernsteinRow.coefficient]

theorem wrong_0011011_edge2_negative_core_corner_arithmetic_poly_tables_5_positive {x : ℝ} (hx : ((133/100) : ℝ) ≤ x ∧ x ≤ (17/10)) :
    0 < wrong_0011011_edge2_negative_core_corner_arithmetic_poly_tables_5.polynomial.eval x :=
  wrong_0011011_edge2_negative_core_corner_arithmetic_poly_tables_5_valid.positive (by norm_num) hx

/-- Source: wrong_0011011_edge2_negative_core_corner_arithmetic.json, polynomial poly_tables_6. -/
def wrong_0011011_edge2_negative_core_corner_arithmetic_poly_tables_6 : Arithmetic.BernsteinRow :=
  { interval := ⟨(133/100),(17/10)⟩
    polynomial := [(1772453513/5000000000), (911372049/2500000000), (1937733623/5000000000)]
    degree := 2
    coefficients := [(76243601690647/50000000000000), (8915126543073/5000000000000), (1047116865007/500000000000)] }

theorem wrong_0011011_edge2_negative_core_corner_arithmetic_poly_tables_6_valid : wrong_0011011_edge2_negative_core_corner_arithmetic_poly_tables_6.Valid (76243601690647/100000000000000) := by
  constructor
  · norm_num [wrong_0011011_edge2_negative_core_corner_arithmetic_poly_tables_6]
  · rfl
  · intro t
    norm_num [wrong_0011011_edge2_negative_core_corner_arithmetic_poly_tables_6, Arithmetic.QPoly.eval, Arithmetic.bernsteinEval,
      Arithmetic.bernsteinBasis, Arithmetic.BernsteinRow.coefficient,
      Finset.sum_range_succ]
    ring
  · intro i hi
    have hi' : i ≤ 2 := hi
    interval_cases i <;> norm_num [wrong_0011011_edge2_negative_core_corner_arithmetic_poly_tables_6,Arithmetic.BernsteinRow.coefficient]

theorem wrong_0011011_edge2_negative_core_corner_arithmetic_poly_tables_6_positive {x : ℝ} (hx : ((133/100) : ℝ) ≤ x ∧ x ≤ (17/10)) :
    0 < wrong_0011011_edge2_negative_core_corner_arithmetic_poly_tables_6.polynomial.eval x :=
  wrong_0011011_edge2_negative_core_corner_arithmetic_poly_tables_6_valid.positive (by norm_num) hx

/-- Source: wrong_0011011_edge2_negative_core_corner_arithmetic.json, polynomial poly_tables_7. -/
def wrong_0011011_edge2_negative_core_corner_arithmetic_poly_tables_7 : Arithmetic.BernsteinRow :=
  { interval := ⟨(133/100),(17/10)⟩
    polynomial := [(19067991973915201132790241055739/12500000000000000000000000000000), (38115774756608630503664169634017/31250000000000000000000000000000), (18145497954552770931697230078167/18750000000000000000000000000000), (95787058619457757986567929949663/125000000000000000000000000000000), (1601943874679094311660636481440773/2625000000000000000000000000000000), (129516769782226241409020911822157/262500000000000000000000000000000), (12775044403185839685995306281679/31250000000000000000000000000000), (131079696245621987422318706681323/375000000000000000000000000000000), (28986639448875194294437420826179/93750000000000000000000000000000), (44094918986274339407658793121/156250000000000000000000000000), (25808680250225707368569365481/97656250000000000000000000000)]
    degree := 10
    coefficients := [(261132777375603773241243204282826078080571745673719/9765625000000000000000000000000000000000000000000), (1466006494413326229770056098029459398122077106811043/46875000000000000000000000000000000000000000000000), (775315723032548205698770566713414188195354766038331/21093750000000000000000000000000000000000000000000), (65095058134002256267941233433399118409763329210923/1500000000000000000000000000000000000000000000000), (1418430885321814386456200898467483550469908962783849/27562500000000000000000000000000000000000000000000), (337805970706593710718235650879738791172572000412353/5512500000000000000000000000000000000000000000000), (2884421351514935322123105772339300483929425788523/39375000000000000000000000000000000000000000000), (1384275578663373388226914888794852539532446512057/15750000000000000000000000000000000000000000000), (1388754787984870084506492748983115770399528743/13125000000000000000000000000000000000000000), (559072227905702905301356394343898916502794147/4375000000000000000000000000000000000000000), (33859753734480528629081002160910202578806541/218750000000000000000000000000000000000000)] }

theorem wrong_0011011_edge2_negative_core_corner_arithmetic_poly_tables_7_valid : wrong_0011011_edge2_negative_core_corner_arithmetic_poly_tables_7.Valid (261132777375603773241243204282826078080571745673719/19531250000000000000000000000000000000000000000000) := by
  constructor
  · norm_num [wrong_0011011_edge2_negative_core_corner_arithmetic_poly_tables_7]
  · rfl
  · intro t
    norm_num [wrong_0011011_edge2_negative_core_corner_arithmetic_poly_tables_7, Arithmetic.QPoly.eval, Arithmetic.bernsteinEval,
      Arithmetic.bernsteinBasis, Arithmetic.BernsteinRow.coefficient,
      Finset.sum_range_succ]
    ring
  · intro i hi
    have hi' : i ≤ 10 := hi
    interval_cases i <;> norm_num [wrong_0011011_edge2_negative_core_corner_arithmetic_poly_tables_7,Arithmetic.BernsteinRow.coefficient]

theorem wrong_0011011_edge2_negative_core_corner_arithmetic_poly_tables_7_positive {x : ℝ} (hx : ((133/100) : ℝ) ≤ x ∧ x ≤ (17/10)) :
    0 < wrong_0011011_edge2_negative_core_corner_arithmetic_poly_tables_7.polynomial.eval x :=
  wrong_0011011_edge2_negative_core_corner_arithmetic_poly_tables_7_valid.positive (by norm_num) hx

/-- Source: CENTRAL_BAND_COMMON_POINT_LEMMAS.md, polynomial segment P, row 0. -/
def central_segment_P0 : Arithmetic.BernsteinRow :=
  { interval := ⟨0,(1/4)⟩
    polynomial := [(721/90000), (3/20), (7379/90000), (-11/3), (589379/90000), (43/60), (-329279/90000)]
    degree := 6
    coefficients := [(721/90000), (2567/180000), (450419/21600000), (89717/3600000), (8746403/345600000), (208973/9216000), (30689/1638400)] }

theorem central_segment_P0_valid : central_segment_P0.Valid (721/180000) := by
  constructor
  · norm_num [central_segment_P0]
  · rfl
  · intro t
    norm_num [central_segment_P0, Arithmetic.QPoly.eval, Arithmetic.bernsteinEval,
      Arithmetic.bernsteinBasis, Arithmetic.BernsteinRow.coefficient,
      Finset.sum_range_succ]
    ring
  · intro i hi
    have hi' : i ≤ 6 := hi
    interval_cases i <;> norm_num [central_segment_P0,Arithmetic.BernsteinRow.coefficient]

theorem central_segment_P0_positive {x : ℝ} (hx : (0 : ℝ) ≤ x ∧ x ≤ (1/4)) :
    0 < central_segment_P0.polynomial.eval x :=
  central_segment_P0_valid.positive (by norm_num) hx

/-- Source: CENTRAL_BAND_COMMON_POINT_LEMMAS.md, polynomial segment P, row 1. -/
def central_segment_P1 : Arithmetic.BernsteinRow :=
  { interval := ⟨(1/4),(1/2)⟩
    polynomial := [(721/90000), (3/20), (7379/90000), (-11/3), (589379/90000), (43/60), (-329279/90000)]
    degree := 6
    coefficients := [(30689/1638400), (545113/36864000), (13177187/1382400000), (119661/25600000), (205099/69120000), (85637/11520000), (2521/128000)] }

theorem central_segment_P1_valid : central_segment_P1.Valid (205099/138240000) := by
  constructor
  · norm_num [central_segment_P1]
  · rfl
  · intro t
    norm_num [central_segment_P1, Arithmetic.QPoly.eval, Arithmetic.bernsteinEval,
      Arithmetic.bernsteinBasis, Arithmetic.BernsteinRow.coefficient,
      Finset.sum_range_succ]
    ring
  · intro i hi
    have hi' : i ≤ 6 := hi
    interval_cases i <;> norm_num [central_segment_P1,Arithmetic.BernsteinRow.coefficient]

theorem central_segment_P1_positive {x : ℝ} (hx : ((1/4) : ℝ) ≤ x ∧ x ≤ (1/2)) :
    0 < central_segment_P1.polynomial.eval x :=
  central_segment_P1_valid.positive (by norm_num) hx

/-- Source: CENTRAL_BAND_COMMON_POINT_LEMMAS.md, polynomial segment P, row 2. -/
def central_segment_P2 : Arithmetic.BernsteinRow :=
  { interval := ⟨(1/2),1⟩
    polynomial := [(721/90000), (3/20), (7379/90000), (-11/3), (589379/90000), (43/60), (-329279/90000)]
    degree := 6
    coefficients := [(2521/128000), (127349/2880000), (215831/2160000), (119867/600000), (451367/1350000), (251/600), (9/50)] }

theorem central_segment_P2_valid : central_segment_P2.Valid (2521/256000) := by
  constructor
  · norm_num [central_segment_P2]
  · rfl
  · intro t
    norm_num [central_segment_P2, Arithmetic.QPoly.eval, Arithmetic.bernsteinEval,
      Arithmetic.bernsteinBasis, Arithmetic.BernsteinRow.coefficient,
      Finset.sum_range_succ]
    ring
  · intro i hi
    have hi' : i ≤ 6 := hi
    interval_cases i <;> norm_num [central_segment_P2,Arithmetic.BernsteinRow.coefficient]

theorem central_segment_P2_positive {x : ℝ} (hx : ((1/2) : ℝ) ≤ x ∧ x ≤ 1) :
    0 < central_segment_P2.polynomial.eval x :=
  central_segment_P2_valid.positive (by norm_num) hx

/-- Source: CENTRAL_BAND_COMMON_POINT_LEMMAS.md, polynomial segment V, row 0. -/
def central_segment_V0 : Arithmetic.BernsteinRow :=
  { interval := ⟨0,(3/14)⟩
    polynomial := [(3/20), (-5/6), (7/10), (17/6), (-17/20)]
    degree := 4
    coefficients := [(3/20), (59/560), (37/560), (4293/109760), (22787/768320)] }

theorem central_segment_V0_valid : central_segment_V0.Valid (22787/1536640) := by
  constructor
  · norm_num [central_segment_V0]
  · rfl
  · intro t
    norm_num [central_segment_V0, Arithmetic.QPoly.eval, Arithmetic.bernsteinEval,
      Arithmetic.bernsteinBasis, Arithmetic.BernsteinRow.coefficient,
      Finset.sum_range_succ]
    ring
  · intro i hi
    have hi' : i ≤ 4 := hi
    interval_cases i <;> norm_num [central_segment_V0,Arithmetic.BernsteinRow.coefficient]

theorem central_segment_V0_positive {x : ℝ} (hx : (0 : ℝ) ≤ x ∧ x ≤ (3/14)) :
    0 < central_segment_V0.polynomial.eval x :=
  central_segment_V0_valid.positive (by norm_num) hx

/-- Source: CENTRAL_BAND_COMMON_POINT_LEMMAS.md, polynomial segment V, row 1. -/
def central_segment_V1 : Arithmetic.BernsteinRow :=
  { interval := ⟨(3/14),(3/7)⟩
    polynomial := [(3/20), (-5/6), (7/10), (17/6), (-17/20)]
    degree := 4
    coefficients := [(22787/768320), (15523/768320), (5427/192080), (1133/19208), (278/2401)] }

theorem central_segment_V1_valid : central_segment_V1.Valid (15523/1536640) := by
  constructor
  · norm_num [central_segment_V1]
  · rfl
  · intro t
    norm_num [central_segment_V1, Arithmetic.QPoly.eval, Arithmetic.bernsteinEval,
      Arithmetic.bernsteinBasis, Arithmetic.BernsteinRow.coefficient,
      Finset.sum_range_succ]
    ring
  · intro i hi
    have hi' : i ≤ 4 := hi
    interval_cases i <;> norm_num [central_segment_V1,Arithmetic.BernsteinRow.coefficient]

theorem central_segment_V1_positive {x : ℝ} (hx : ((3/14) : ℝ) ≤ x ∧ x ≤ (3/7)) :
    0 < central_segment_V1.polynomial.eval x :=
  central_segment_V1_valid.positive (by norm_num) hx

/-- Source: CENTRAL_BAND_COMMON_POINT_LEMMAS.md, polynomial bandA P, row 0. -/
def central_bandA_P0 : Arithmetic.BernsteinRow :=
  { interval := ⟨0,(1/4)⟩
    polynomial := [(2540913450225412921/39062500000000000000), (117708140112740701/3125000000000000000), (4442784786036443889/625000000000000000000), (-5821802411/1562500000), (4161617771686036443889/625000000000000000000), (2383626569387259299/3125000000000000000), (-143004146824774587079/39062500000000000000)]
    degree := 6
    coefficients := [(2540913450225412921/39062500000000000000), (124906549113638337733/1875000000000000000000), (10232382994102584864529/150000000000000000000000), (3346683221025046384769/50000000000000000000000), (49274612618208571550491/800000000000000000000000), (1269022836132573026803/24000000000000000000000), (17020603344683950553/400000000000000000000)] }

theorem central_bandA_P0_valid : central_bandA_P0.Valid (17020603344683950553/800000000000000000000) := by
  constructor
  · norm_num [central_bandA_P0]
  · rfl
  · intro t
    norm_num [central_bandA_P0, Arithmetic.QPoly.eval, Arithmetic.bernsteinEval,
      Arithmetic.bernsteinBasis, Arithmetic.BernsteinRow.coefficient,
      Finset.sum_range_succ]
    ring
  · intro i hi
    have hi' : i ≤ 6 := hi
    interval_cases i <;> norm_num [central_bandA_P0,Arithmetic.BernsteinRow.coefficient]

theorem central_bandA_P0_positive {x : ℝ} (hx : (0 : ℝ) ≤ x ∧ x ≤ (1/4)) :
    0 < central_bandA_P0.polynomial.eval x :=
  central_bandA_P0_valid.positive (by norm_num) hx

/-- Source: CENTRAL_BAND_COMMON_POINT_LEMMAS.md, polynomial bandA P, row 1. -/
def central_bandA_P1 : Arithmetic.BernsteinRow :=
  { interval := ⟨(1/4),(3/8)⟩
    polynomial := [(2540913450225412921/39062500000000000000), (117708140112740701/3125000000000000000), (4442784786036443889/625000000000000000000), (-5821802411/1562500000), (4161617771686036443889/625000000000000000000), (2383626569387259299/3125000000000000000), (-143004146824774587079/39062500000000000000)]
    degree := 6
    coefficients := [(17020603344683950553/400000000000000000000), (1794685765910538072737/48000000000000000000000), (101840905596005076143891/3200000000000000000000000), (33383322024218801507483/1280000000000000000000000), (392541216014807255335331/19200000000000000000000000), (23425421096397963792737/1536000000000000000000000), (4439300063959196787073/409600000000000000000000)] }

theorem central_bandA_P1_valid : central_bandA_P1.Valid (4439300063959196787073/819200000000000000000000) := by
  constructor
  · norm_num [central_bandA_P1]
  · rfl
  · intro t
    norm_num [central_bandA_P1, Arithmetic.QPoly.eval, Arithmetic.bernsteinEval,
      Arithmetic.bernsteinBasis, Arithmetic.BernsteinRow.coefficient,
      Finset.sum_range_succ]
    ring
  · intro i hi
    have hi' : i ≤ 6 := hi
    interval_cases i <;> norm_num [central_bandA_P1,Arithmetic.BernsteinRow.coefficient]

theorem central_bandA_P1_positive {x : ℝ} (hx : ((1/4) : ℝ) ≤ x ∧ x ≤ (3/8)) :
    0 < central_bandA_P1.polynomial.eval x :=
  central_bandA_P1_valid.positive (by norm_num) hx

/-- Source: CENTRAL_BAND_COMMON_POINT_LEMMAS.md, polynomial bandA P, row 2. -/
def central_bandA_P2 : Arithmetic.BernsteinRow :=
  { interval := ⟨(3/8),(7/16)⟩
    polynomial := [(2540913450225412921/39062500000000000000), (117708140112740701/3125000000000000000), (4442784786036443889/625000000000000000000), (-5821802411/1562500000), (4161617771686036443889/625000000000000000000), (2383626569387259299/3125000000000000000), (-143004146824774587079/39062500000000000000)]
    degree := 6
    coefficients := [(4439300063959196787073/409600000000000000000000), (106066818492572000247337/12288000000000000000000000), (4067714786141968923411823/614400000000000000000000000), (1985415032490743810656699/409600000000000000000000000), (549558444919499815651801/163840000000000000000000000), (2146654046558964370104061/983040000000000000000000000), (180262552727933630595469/131072000000000000000000000)] }

theorem central_bandA_P2_valid : central_bandA_P2.Valid (180262552727933630595469/262144000000000000000000000) := by
  constructor
  · norm_num [central_bandA_P2]
  · rfl
  · intro t
    norm_num [central_bandA_P2, Arithmetic.QPoly.eval, Arithmetic.bernsteinEval,
      Arithmetic.bernsteinBasis, Arithmetic.BernsteinRow.coefficient,
      Finset.sum_range_succ]
    ring
  · intro i hi
    have hi' : i ≤ 6 := hi
    interval_cases i <;> norm_num [central_bandA_P2,Arithmetic.BernsteinRow.coefficient]

theorem central_bandA_P2_positive {x : ℝ} (hx : ((3/8) : ℝ) ≤ x ∧ x ≤ (7/16)) :
    0 < central_bandA_P2.polynomial.eval x :=
  central_bandA_P2_valid.positive (by norm_num) hx

/-- Source: CENTRAL_BAND_COMMON_POINT_LEMMAS.md, polynomial bandA P, row 3. -/
def central_bandA_P3 : Arithmetic.BernsteinRow :=
  { interval := ⟨(7/16),(1/2)⟩
    polynomial := [(2540913450225412921/39062500000000000000), (117708140112740701/3125000000000000000), (4442784786036443889/625000000000000000000), (-5821802411/1562500000), (4161617771686036443889/625000000000000000000), (2383626569387259299/3125000000000000000), (-143004146824774587079/39062500000000000000)]
    degree := 6
    coefficients := [(180262552727933630595469/131072000000000000000000000), (278642122180020044413987/491520000000000000000000000), (14826383139893791419829/122880000000000000000000000), (1953451669079521155421/25600000000000000000000000), (452507753787127338707/960000000000000000000000), (13397119863903505241/10000000000000000000000), (5419983821580126081/2000000000000000000000)] }

theorem central_bandA_P3_valid : central_bandA_P3.Valid (1953451669079521155421/51200000000000000000000000) := by
  constructor
  · norm_num [central_bandA_P3]
  · rfl
  · intro t
    norm_num [central_bandA_P3, Arithmetic.QPoly.eval, Arithmetic.bernsteinEval,
      Arithmetic.bernsteinBasis, Arithmetic.BernsteinRow.coefficient,
      Finset.sum_range_succ]
    ring
  · intro i hi
    have hi' : i ≤ 6 := hi
    interval_cases i <;> norm_num [central_bandA_P3,Arithmetic.BernsteinRow.coefficient]

theorem central_bandA_P3_positive {x : ℝ} (hx : ((7/16) : ℝ) ≤ x ∧ x ≤ (1/2)) :
    0 < central_bandA_P3.polynomial.eval x :=
  central_bandA_P3_valid.positive (by norm_num) hx

/-- Source: CENTRAL_BAND_COMMON_POINT_LEMMAS.md, polynomial bandA P, row 4. -/
def central_bandA_P4 : Arithmetic.BernsteinRow :=
  { interval := ⟨(1/2),1⟩
    polynomial := [(2540913450225412921/39062500000000000000), (117708140112740701/3125000000000000000), (4442784786036443889/625000000000000000000), (-5821802411/1562500000), (4161617771686036443889/625000000000000000000), (2383626569387259299/3125000000000000000), (-143004146824774587079/39062500000000000000)]
    degree := 6
    coefficients := [(5419983821580126081/2000000000000000000000), (136722313059877631717/10000000000000000000000), (1702740069587793601717/30000000000000000000000), (3665723121458833105957/25000000000000000000000), (10366293767811381451763/37500000000000000000000), (54687474688075349441/150000000000000000000), (72155839983428881/500000000000000000)] }

theorem central_bandA_P4_valid : central_bandA_P4.Valid (5419983821580126081/4000000000000000000000) := by
  constructor
  · norm_num [central_bandA_P4]
  · rfl
  · intro t
    norm_num [central_bandA_P4, Arithmetic.QPoly.eval, Arithmetic.bernsteinEval,
      Arithmetic.bernsteinBasis, Arithmetic.BernsteinRow.coefficient,
      Finset.sum_range_succ]
    ring
  · intro i hi
    have hi' : i ≤ 6 := hi
    interval_cases i <;> norm_num [central_bandA_P4,Arithmetic.BernsteinRow.coefficient]

theorem central_bandA_P4_positive {x : ℝ} (hx : ((1/2) : ℝ) ≤ x ∧ x ≤ 1) :
    0 < central_bandA_P4.polynomial.eval x :=
  central_bandA_P4_valid.positive (by norm_num) hx

/-- Source: CENTRAL_BAND_COMMON_POINT_LEMMAS.md, polynomial bandA V, row 0. -/
def central_bandA_V0 : Arithmetic.BernsteinRow :=
  { interval := ⟨0,(3/14)⟩
    polynomial := [(268618391/2000000000), (-43078848583/50000000000), (731381609/1000000000), (143218848583/50000000000), (-1731381609/2000000000)]
    degree := 4
    coefficients := [(268618391/2000000000), (246829201651/2800000000000), (2379734267/50000000000), (10800114775129/548800000000000), (18494556101093/1920800000000000)] }

theorem central_bandA_V0_valid : central_bandA_V0.Valid (18494556101093/3841600000000000) := by
  constructor
  · norm_num [central_bandA_V0]
  · rfl
  · intro t
    norm_num [central_bandA_V0, Arithmetic.QPoly.eval, Arithmetic.bernsteinEval,
      Arithmetic.bernsteinBasis, Arithmetic.BernsteinRow.coefficient,
      Finset.sum_range_succ]
    ring
  · intro i hi
    have hi' : i ≤ 4 := hi
    interval_cases i <;> norm_num [central_bandA_V0,Arithmetic.BernsteinRow.coefficient]

theorem central_bandA_V0_positive {x : ℝ} (hx : (0 : ℝ) ≤ x ∧ x ≤ (3/14)) :
    0 < central_bandA_V0.polynomial.eval x :=
  central_bandA_V0_valid.positive (by norm_num) hx

/-- Source: CENTRAL_BAND_COMMON_POINT_LEMMAS.md, polynomial bandA V, row 1. -/
def central_bandA_V1 : Arithmetic.BernsteinRow :=
  { interval := ⟨(3/14),(9/28)⟩
    polynomial := [(268618391/2000000000), (-43078848583/50000000000), (731381609/1000000000), (143218848583/50000000000), (-1731381609/2000000000)]
    degree := 4
    coefficients := [(18494556101093/1920800000000000), (7073306636131/1536640000000000), (77671165583/19208000000000), (52878472222753/6146560000000000), (578371840373027/30732800000000000)] }

theorem central_bandA_V1_valid : central_bandA_V1.Valid (77671165583/38416000000000) := by
  constructor
  · norm_num [central_bandA_V1]
  · rfl
  · intro t
    norm_num [central_bandA_V1, Arithmetic.QPoly.eval, Arithmetic.bernsteinEval,
      Arithmetic.bernsteinBasis, Arithmetic.BernsteinRow.coefficient,
      Finset.sum_range_succ]
    ring
  · intro i hi
    have hi' : i ≤ 4 := hi
    interval_cases i <;> norm_num [central_bandA_V1,Arithmetic.BernsteinRow.coefficient]

theorem central_bandA_V1_positive {x : ℝ} (hx : ((3/14) : ℝ) ≤ x ∧ x ≤ (9/28)) :
    0 < central_bandA_V1.polynomial.eval x :=
  central_bandA_V1_valid.positive (by norm_num) hx

/-- Source: CENTRAL_BAND_COMMON_POINT_LEMMAS.md, polynomial bandA V, row 2. -/
def central_bandA_V2 : Arithmetic.BernsteinRow :=
  { interval := ⟨(9/28),(3/7)⟩
    polynomial := [(268618391/2000000000), (-43078848583/50000000000), (731381609/1000000000), (143218848583/50000000000), (-1731381609/2000000000)]
    degree := 4
    coefficients := [(578371840373027/30732800000000000), (892351319632289/30732800000000000), (172523972746231/3841600000000000), (64326357702913/960400000000000), (287124070757/3001250000000)] }

theorem central_bandA_V2_valid : central_bandA_V2.Valid (578371840373027/61465600000000000) := by
  constructor
  · norm_num [central_bandA_V2]
  · rfl
  · intro t
    norm_num [central_bandA_V2, Arithmetic.QPoly.eval, Arithmetic.bernsteinEval,
      Arithmetic.bernsteinBasis, Arithmetic.BernsteinRow.coefficient,
      Finset.sum_range_succ]
    ring
  · intro i hi
    have hi' : i ≤ 4 := hi
    interval_cases i <;> norm_num [central_bandA_V2,Arithmetic.BernsteinRow.coefficient]

theorem central_bandA_V2_positive {x : ℝ} (hx : ((9/28) : ℝ) ≤ x ∧ x ≤ (3/7)) :
    0 < central_bandA_V2.polynomial.eval x :=
  central_bandA_V2_valid.positive (by norm_num) hx

/-- Source: CENTRAL_BAND_COMMON_POINT_LEMMAS.md, polynomial bandB P, row 0. -/
def central_bandB_P0 : Arithmetic.BernsteinRow :=
  { interval := ⟨0,(1/2)⟩
    polynomial := [(5759271769/40000000000), (-130551593/2000000000), (-3465819669/40000000000), (-190363/50000), (270512580331/40000000000), (1660671593/2000000000), (-146531128231/40000000000)]
    degree := 6
    coefficients := [(5759271769/40000000000), (8312528671/60000000000), (315980167871/2400000000000), (79628156411/800000000000), (89386636807/1920000000000), (384220597/40000000000), (2642023161/512000000000)] }

theorem central_bandB_P0_valid : central_bandB_P0.Valid (2642023161/1024000000000) := by
  constructor
  · norm_num [central_bandB_P0]
  · rfl
  · intro t
    norm_num [central_bandB_P0, Arithmetic.QPoly.eval, Arithmetic.bernsteinEval,
      Arithmetic.bernsteinBasis, Arithmetic.BernsteinRow.coefficient,
      Finset.sum_range_succ]
    ring
  · intro i hi
    have hi' : i ≤ 6 := hi
    interval_cases i <;> norm_num [central_bandB_P0,Arithmetic.BernsteinRow.coefficient]

theorem central_bandB_P0_positive {x : ℝ} (hx : (0 : ℝ) ≤ x ∧ x ≤ (1/2)) :
    0 < central_bandB_P0.polynomial.eval x :=
  central_bandB_P0_valid.positive (by norm_num) hx

/-- Source: CENTRAL_BAND_COMMON_POINT_LEMMAS.md, polynomial bandB P, row 1. -/
def central_bandB_P1 : Arithmetic.BernsteinRow :=
  { interval := ⟨(1/2),1⟩
    polynomial := [(5759271769/40000000000), (-130551593/2000000000), (-3465819669/40000000000), (-190363/50000), (270512580331/40000000000), (1660671593/2000000000), (-146531128231/40000000000)]
    degree := 6
    coefficients := [(2642023161/512000000000), (915056701/1280000000000), (27623314799/960000000000), (84650781839/800000000000), (136737927263/600000000000), (3813150259/12000000000), (22934521/200000000)] }

theorem central_bandB_P1_valid : central_bandB_P1.Valid (915056701/2560000000000) := by
  constructor
  · norm_num [central_bandB_P1]
  · rfl
  · intro t
    norm_num [central_bandB_P1, Arithmetic.QPoly.eval, Arithmetic.bernsteinEval,
      Arithmetic.bernsteinBasis, Arithmetic.BernsteinRow.coefficient,
      Finset.sum_range_succ]
    ring
  · intro i hi
    have hi' : i ≤ 6 := hi
    interval_cases i <;> norm_num [central_bandB_P1,Arithmetic.BernsteinRow.coefficient]

theorem central_bandB_P1_positive {x : ℝ} (hx : ((1/2) : ℝ) ≤ x ∧ x ≤ 1) :
    0 < central_bandB_P1.polynomial.eval x :=
  central_bandB_P1_valid.positive (by norm_num) hx

end SquaresInCircles.Eight.Generated
