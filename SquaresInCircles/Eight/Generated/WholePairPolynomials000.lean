module

public import SquaresInCircles.Eight.Arithmetic.BernsteinCheck

/-!
# Eight squares: the polynomial rows of the central band

The polynomials `centralBandP` and `centralBandV` of
`Arithmetic/CentralBandPolynomials.lean` for `transverse_segment_sides`, `bandA_sides`
and `bandB_sides` of `CentralCore.lean`, expanded in powers of the half-angle tangent
`u`, each on the pieces of a cut of its interval: `[0, 1]` for `centralBandP` and
`[0, 3/7]` for `centralBandV`. A row (`Arithmetic.BernsteinRow`) holds the expansion,
the piece and the exact Bernstein coefficients there. The kernel checks each row by
`BernsteinRow.check` (`_valid`), and its positive coefficients make the polynomial
positive on the piece (`_positive`). `Arithmetic/CentralBandPolynomials.lean`
identifies each expansion with its polynomial and joins the pieces. Written by
`scripts/eight/generate_polynomial_rows.py`.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.Generated

/-- The polynomial `centralBandP (11/12) (7/20)` for `transverse_segment_sides`,
expanded in powers of `u`, on `[0, 1/4]`. -/
def central_segment_P0 : Arithmetic.BernsteinRow :=
  { interval := ⟨0,(1/4)⟩
    polynomial := [(721/90000), (3/20), (7379/90000), (-11/3), (589379/90000), (43/60), (-329279/90000)]
    degree := 6
    coefficients := [(721/90000), (2567/180000), (450419/21600000), (89717/3600000), (8746403/345600000), (208973/9216000), (30689/1638400)] }

theorem central_segment_P0_valid : central_segment_P0.Valid (721/180000) :=
  Arithmetic.BernsteinRow.valid_of_check (by decide +kernel)
theorem central_segment_P0_positive {x : ℝ} (hx : (0 : ℝ) ≤ x ∧ x ≤ (1/4)) :
    0 < central_segment_P0.polynomial.eval x :=
  central_segment_P0_valid.positive_of_eq (by norm_num) rfl (by push_cast; exact hx)
/-- The polynomial `centralBandP (11/12) (7/20)` for `transverse_segment_sides`,
expanded in powers of `u`, on `[1/4, 1/2]`. -/
def central_segment_P1 : Arithmetic.BernsteinRow :=
  { interval := ⟨(1/4),(1/2)⟩
    polynomial := [(721/90000), (3/20), (7379/90000), (-11/3), (589379/90000), (43/60), (-329279/90000)]
    degree := 6
    coefficients := [(30689/1638400), (545113/36864000), (13177187/1382400000), (119661/25600000), (205099/69120000), (85637/11520000), (2521/128000)] }

theorem central_segment_P1_valid : central_segment_P1.Valid (205099/138240000) :=
  Arithmetic.BernsteinRow.valid_of_check (by decide +kernel)
theorem central_segment_P1_positive {x : ℝ} (hx : ((1/4) : ℝ) ≤ x ∧ x ≤ (1/2)) :
    0 < central_segment_P1.polynomial.eval x :=
  central_segment_P1_valid.positive_of_eq (by norm_num) rfl (by push_cast; exact hx)
/-- The polynomial `centralBandP (11/12) (7/20)` for `transverse_segment_sides`,
expanded in powers of `u`, on `[1/2, 1]`. -/
def central_segment_P2 : Arithmetic.BernsteinRow :=
  { interval := ⟨(1/2),1⟩
    polynomial := [(721/90000), (3/20), (7379/90000), (-11/3), (589379/90000), (43/60), (-329279/90000)]
    degree := 6
    coefficients := [(2521/128000), (127349/2880000), (215831/2160000), (119867/600000), (451367/1350000), (251/600), (9/50)] }

theorem central_segment_P2_valid : central_segment_P2.Valid (2521/256000) :=
  Arithmetic.BernsteinRow.valid_of_check (by decide +kernel)
theorem central_segment_P2_positive {x : ℝ} (hx : ((1/2) : ℝ) ≤ x ∧ x ≤ 1) :
    0 < central_segment_P2.polynomial.eval x :=
  central_segment_P2_valid.positive_of_eq (by norm_num) rfl (by push_cast; exact hx)
/-- The polynomial `centralBandV (1/2) (11/12) (7/20)` for `transverse_segment_sides`,
expanded in powers of `u`, on `[0, 3/14]`. -/
def central_segment_V0 : Arithmetic.BernsteinRow :=
  { interval := ⟨0,(3/14)⟩
    polynomial := [(3/20), (-5/6), (7/10), (17/6), (-17/20)]
    degree := 4
    coefficients := [(3/20), (59/560), (37/560), (4293/109760), (22787/768320)] }

theorem central_segment_V0_valid : central_segment_V0.Valid (22787/1536640) :=
  Arithmetic.BernsteinRow.valid_of_check (by decide +kernel)
theorem central_segment_V0_positive {x : ℝ} (hx : (0 : ℝ) ≤ x ∧ x ≤ (3/14)) :
    0 < central_segment_V0.polynomial.eval x :=
  central_segment_V0_valid.positive_of_eq (by norm_num) rfl (by push_cast; exact hx)
/-- The polynomial `centralBandV (1/2) (11/12) (7/20)` for `transverse_segment_sides`,
expanded in powers of `u`, on `[3/14, 3/7]`. -/
def central_segment_V1 : Arithmetic.BernsteinRow :=
  { interval := ⟨(3/14),(3/7)⟩
    polynomial := [(3/20), (-5/6), (7/10), (17/6), (-17/20)]
    degree := 4
    coefficients := [(22787/768320), (15523/768320), (5427/192080), (1133/19208), (278/2401)] }

theorem central_segment_V1_valid : central_segment_V1.Valid (15523/1536640) :=
  Arithmetic.BernsteinRow.valid_of_check (by decide +kernel)
theorem central_segment_V1_positive {x : ℝ} (hx : ((3/14) : ℝ) ≤ x ∧ x ≤ (3/7)) :
    0 < central_segment_V1.polynomial.eval x :=
  central_segment_V1_valid.positive_of_eq (by norm_num) rfl (by push_cast; exact hx)
/-- The polynomial `centralBandP bandA_Cminus bandA_D` for `bandA_sides`,
expanded in powers of `u`, on `[0, 1/4]`. -/
def central_bandA_P0 : Arithmetic.BernsteinRow :=
  { interval := ⟨0,(1/4)⟩
    polynomial := [(2540913450225412921/39062500000000000000), (117708140112740701/3125000000000000000), (4442784786036443889/625000000000000000000), (-5821802411/1562500000), (4161617771686036443889/625000000000000000000), (2383626569387259299/3125000000000000000), (-143004146824774587079/39062500000000000000)]
    degree := 6
    coefficients := [(2540913450225412921/39062500000000000000), (124906549113638337733/1875000000000000000000), (10232382994102584864529/150000000000000000000000), (3346683221025046384769/50000000000000000000000), (49274612618208571550491/800000000000000000000000), (1269022836132573026803/24000000000000000000000), (17020603344683950553/400000000000000000000)] }

theorem central_bandA_P0_valid : central_bandA_P0.Valid (17020603344683950553/800000000000000000000) :=
  Arithmetic.BernsteinRow.valid_of_check (by decide +kernel)
theorem central_bandA_P0_positive {x : ℝ} (hx : (0 : ℝ) ≤ x ∧ x ≤ (1/4)) :
    0 < central_bandA_P0.polynomial.eval x :=
  central_bandA_P0_valid.positive_of_eq (by norm_num) rfl (by push_cast; exact hx)
/-- The polynomial `centralBandP bandA_Cminus bandA_D` for `bandA_sides`,
expanded in powers of `u`, on `[1/4, 3/8]`. -/
def central_bandA_P1 : Arithmetic.BernsteinRow :=
  { interval := ⟨(1/4),(3/8)⟩
    polynomial := [(2540913450225412921/39062500000000000000), (117708140112740701/3125000000000000000), (4442784786036443889/625000000000000000000), (-5821802411/1562500000), (4161617771686036443889/625000000000000000000), (2383626569387259299/3125000000000000000), (-143004146824774587079/39062500000000000000)]
    degree := 6
    coefficients := [(17020603344683950553/400000000000000000000), (1794685765910538072737/48000000000000000000000), (101840905596005076143891/3200000000000000000000000), (33383322024218801507483/1280000000000000000000000), (392541216014807255335331/19200000000000000000000000), (23425421096397963792737/1536000000000000000000000), (4439300063959196787073/409600000000000000000000)] }

theorem central_bandA_P1_valid : central_bandA_P1.Valid (4439300063959196787073/819200000000000000000000) :=
  Arithmetic.BernsteinRow.valid_of_check (by decide +kernel)
theorem central_bandA_P1_positive {x : ℝ} (hx : ((1/4) : ℝ) ≤ x ∧ x ≤ (3/8)) :
    0 < central_bandA_P1.polynomial.eval x :=
  central_bandA_P1_valid.positive_of_eq (by norm_num) rfl (by push_cast; exact hx)
/-- The polynomial `centralBandP bandA_Cminus bandA_D` for `bandA_sides`,
expanded in powers of `u`, on `[3/8, 7/16]`. -/
def central_bandA_P2 : Arithmetic.BernsteinRow :=
  { interval := ⟨(3/8),(7/16)⟩
    polynomial := [(2540913450225412921/39062500000000000000), (117708140112740701/3125000000000000000), (4442784786036443889/625000000000000000000), (-5821802411/1562500000), (4161617771686036443889/625000000000000000000), (2383626569387259299/3125000000000000000), (-143004146824774587079/39062500000000000000)]
    degree := 6
    coefficients := [(4439300063959196787073/409600000000000000000000), (106066818492572000247337/12288000000000000000000000), (4067714786141968923411823/614400000000000000000000000), (1985415032490743810656699/409600000000000000000000000), (549558444919499815651801/163840000000000000000000000), (2146654046558964370104061/983040000000000000000000000), (180262552727933630595469/131072000000000000000000000)] }

theorem central_bandA_P2_valid : central_bandA_P2.Valid (180262552727933630595469/262144000000000000000000000) :=
  Arithmetic.BernsteinRow.valid_of_check (by decide +kernel)
theorem central_bandA_P2_positive {x : ℝ} (hx : ((3/8) : ℝ) ≤ x ∧ x ≤ (7/16)) :
    0 < central_bandA_P2.polynomial.eval x :=
  central_bandA_P2_valid.positive_of_eq (by norm_num) rfl (by push_cast; exact hx)
/-- The polynomial `centralBandP bandA_Cminus bandA_D` for `bandA_sides`,
expanded in powers of `u`, on `[7/16, 1/2]`. -/
def central_bandA_P3 : Arithmetic.BernsteinRow :=
  { interval := ⟨(7/16),(1/2)⟩
    polynomial := [(2540913450225412921/39062500000000000000), (117708140112740701/3125000000000000000), (4442784786036443889/625000000000000000000), (-5821802411/1562500000), (4161617771686036443889/625000000000000000000), (2383626569387259299/3125000000000000000), (-143004146824774587079/39062500000000000000)]
    degree := 6
    coefficients := [(180262552727933630595469/131072000000000000000000000), (278642122180020044413987/491520000000000000000000000), (14826383139893791419829/122880000000000000000000000), (1953451669079521155421/25600000000000000000000000), (452507753787127338707/960000000000000000000000), (13397119863903505241/10000000000000000000000), (5419983821580126081/2000000000000000000000)] }

theorem central_bandA_P3_valid : central_bandA_P3.Valid (1953451669079521155421/51200000000000000000000000) :=
  Arithmetic.BernsteinRow.valid_of_check (by decide +kernel)
theorem central_bandA_P3_positive {x : ℝ} (hx : ((7/16) : ℝ) ≤ x ∧ x ≤ (1/2)) :
    0 < central_bandA_P3.polynomial.eval x :=
  central_bandA_P3_valid.positive_of_eq (by norm_num) rfl (by push_cast; exact hx)
/-- The polynomial `centralBandP bandA_Cminus bandA_D` for `bandA_sides`,
expanded in powers of `u`, on `[1/2, 1]`. -/
def central_bandA_P4 : Arithmetic.BernsteinRow :=
  { interval := ⟨(1/2),1⟩
    polynomial := [(2540913450225412921/39062500000000000000), (117708140112740701/3125000000000000000), (4442784786036443889/625000000000000000000), (-5821802411/1562500000), (4161617771686036443889/625000000000000000000), (2383626569387259299/3125000000000000000), (-143004146824774587079/39062500000000000000)]
    degree := 6
    coefficients := [(5419983821580126081/2000000000000000000000), (136722313059877631717/10000000000000000000000), (1702740069587793601717/30000000000000000000000), (3665723121458833105957/25000000000000000000000), (10366293767811381451763/37500000000000000000000), (54687474688075349441/150000000000000000000), (72155839983428881/500000000000000000)] }

theorem central_bandA_P4_valid : central_bandA_P4.Valid (5419983821580126081/4000000000000000000000) :=
  Arithmetic.BernsteinRow.valid_of_check (by decide +kernel)
theorem central_bandA_P4_positive {x : ℝ} (hx : ((1/2) : ℝ) ≤ x ∧ x ≤ 1) :
    0 < central_bandA_P4.polynomial.eval x :=
  central_bandA_P4_valid.positive_of_eq (by norm_num) rfl (by push_cast; exact hx)
/-- The polynomial `centralBandV (5007/10000) bandA_Cplus bandA_D` for `bandA_sides`,
expanded in powers of `u`, on `[0, 3/14]`. -/
def central_bandA_V0 : Arithmetic.BernsteinRow :=
  { interval := ⟨0,(3/14)⟩
    polynomial := [(268618391/2000000000), (-43078848583/50000000000), (731381609/1000000000), (143218848583/50000000000), (-1731381609/2000000000)]
    degree := 4
    coefficients := [(268618391/2000000000), (246829201651/2800000000000), (2379734267/50000000000), (10800114775129/548800000000000), (18494556101093/1920800000000000)] }

theorem central_bandA_V0_valid : central_bandA_V0.Valid (18494556101093/3841600000000000) :=
  Arithmetic.BernsteinRow.valid_of_check (by decide +kernel)
theorem central_bandA_V0_positive {x : ℝ} (hx : (0 : ℝ) ≤ x ∧ x ≤ (3/14)) :
    0 < central_bandA_V0.polynomial.eval x :=
  central_bandA_V0_valid.positive_of_eq (by norm_num) rfl (by push_cast; exact hx)
/-- The polynomial `centralBandV (5007/10000) bandA_Cplus bandA_D` for `bandA_sides`,
expanded in powers of `u`, on `[3/14, 9/28]`. -/
def central_bandA_V1 : Arithmetic.BernsteinRow :=
  { interval := ⟨(3/14),(9/28)⟩
    polynomial := [(268618391/2000000000), (-43078848583/50000000000), (731381609/1000000000), (143218848583/50000000000), (-1731381609/2000000000)]
    degree := 4
    coefficients := [(18494556101093/1920800000000000), (7073306636131/1536640000000000), (77671165583/19208000000000), (52878472222753/6146560000000000), (578371840373027/30732800000000000)] }

theorem central_bandA_V1_valid : central_bandA_V1.Valid (77671165583/38416000000000) :=
  Arithmetic.BernsteinRow.valid_of_check (by decide +kernel)
theorem central_bandA_V1_positive {x : ℝ} (hx : ((3/14) : ℝ) ≤ x ∧ x ≤ (9/28)) :
    0 < central_bandA_V1.polynomial.eval x :=
  central_bandA_V1_valid.positive_of_eq (by norm_num) rfl (by push_cast; exact hx)
/-- The polynomial `centralBandV (5007/10000) bandA_Cplus bandA_D` for `bandA_sides`,
expanded in powers of `u`, on `[9/28, 3/7]`. -/
def central_bandA_V2 : Arithmetic.BernsteinRow :=
  { interval := ⟨(9/28),(3/7)⟩
    polynomial := [(268618391/2000000000), (-43078848583/50000000000), (731381609/1000000000), (143218848583/50000000000), (-1731381609/2000000000)]
    degree := 4
    coefficients := [(578371840373027/30732800000000000), (892351319632289/30732800000000000), (172523972746231/3841600000000000), (64326357702913/960400000000000), (287124070757/3001250000000)] }

theorem central_bandA_V2_valid : central_bandA_V2.Valid (578371840373027/61465600000000000) :=
  Arithmetic.BernsteinRow.valid_of_check (by decide +kernel)
theorem central_bandA_V2_positive {x : ℝ} (hx : ((9/28) : ℝ) ≤ x ∧ x ≤ (3/7)) :
    0 < central_bandA_V2.polynomial.eval x :=
  central_bandA_V2_valid.positive_of_eq (by norm_num) rfl (by push_cast; exact hx)
/-- The polynomial `centralBandP bandB_Cminus bandB_D` for `bandB_sides`,
expanded in powers of `u`, on `[0, 1/2]`. -/
def central_bandB_P0 : Arithmetic.BernsteinRow :=
  { interval := ⟨0,(1/2)⟩
    polynomial := [(5759271769/40000000000), (-130551593/2000000000), (-3465819669/40000000000), (-190363/50000), (270512580331/40000000000), (1660671593/2000000000), (-146531128231/40000000000)]
    degree := 6
    coefficients := [(5759271769/40000000000), (8312528671/60000000000), (315980167871/2400000000000), (79628156411/800000000000), (89386636807/1920000000000), (384220597/40000000000), (2642023161/512000000000)] }

theorem central_bandB_P0_valid : central_bandB_P0.Valid (2642023161/1024000000000) :=
  Arithmetic.BernsteinRow.valid_of_check (by decide +kernel)
theorem central_bandB_P0_positive {x : ℝ} (hx : (0 : ℝ) ≤ x ∧ x ≤ (1/2)) :
    0 < central_bandB_P0.polynomial.eval x :=
  central_bandB_P0_valid.positive_of_eq (by norm_num) rfl (by push_cast; exact hx)
/-- The polynomial `centralBandP bandB_Cminus bandB_D` for `bandB_sides`,
expanded in powers of `u`, on `[1/2, 1]`. -/
def central_bandB_P1 : Arithmetic.BernsteinRow :=
  { interval := ⟨(1/2),1⟩
    polynomial := [(5759271769/40000000000), (-130551593/2000000000), (-3465819669/40000000000), (-190363/50000), (270512580331/40000000000), (1660671593/2000000000), (-146531128231/40000000000)]
    degree := 6
    coefficients := [(2642023161/512000000000), (915056701/1280000000000), (27623314799/960000000000), (84650781839/800000000000), (136737927263/600000000000), (3813150259/12000000000), (22934521/200000000)] }

theorem central_bandB_P1_valid : central_bandB_P1.Valid (915056701/2560000000000) :=
  Arithmetic.BernsteinRow.valid_of_check (by decide +kernel)
theorem central_bandB_P1_positive {x : ℝ} (hx : ((1/2) : ℝ) ≤ x ∧ x ≤ 1) :
    0 < central_bandB_P1.polynomial.eval x :=
  central_bandB_P1_valid.positive_of_eq (by norm_num) rfl (by push_cast; exact hx)
/-- The polynomial `centralBandV (107/200) bandB_Cplus bandB_D` for `bandB_sides`,
expanded in powers of `u`, on `[0, 3/14]`. -/
def central_bandB_V0 : Arithmetic.BernsteinRow :=
  { interval := ⟨0,(3/14)⟩
    polynomial := [(4789/40000), (-166767/200000), (15211/20000), (594767/200000), (-35211/40000)]
    degree := 4
    coefficients := [(4789/40000), (840619/11200000), (101377/2800000), (23033761/2195200000), (25928687/7683200000)] }

theorem central_bandB_V0_valid : central_bandB_V0.Valid (25928687/15366400000) :=
  Arithmetic.BernsteinRow.valid_of_check (by decide +kernel)
theorem central_bandB_V0_positive {x : ℝ} (hx : (0 : ℝ) ≤ x ∧ x ≤ (3/14)) :
    0 < central_bandB_V0.polynomial.eval x :=
  central_bandB_V0_valid.positive_of_eq (by norm_num) rfl (by push_cast; exact hx)
/-- The polynomial `centralBandV (107/200) bandB_Cplus bandB_D` for `bandB_sides`,
expanded in powers of `u`, on `[3/14, 15/56]`. -/
def central_bandB_V1 : Arithmetic.BernsteinRow :=
  { interval := ⟨(3/14),(15/56)⟩
    polynomial := [(4789/40000), (-166767/200000), (15211/20000), (594767/200000), (-35211/40000)]
    degree := 4
    coefficients := [(25928687/7683200000), (98050543/61465600000), (30053507/30732800000), (1581472597/983449600000), (1401939853/393379840000)] }

theorem central_bandB_V1_valid : central_bandB_V1.Valid (30053507/61465600000) :=
  Arithmetic.BernsteinRow.valid_of_check (by decide +kernel)
theorem central_bandB_V1_positive {x : ℝ} (hx : ((3/14) : ℝ) ≤ x ∧ x ≤ (15/56)) :
    0 < central_bandB_V1.polynomial.eval x :=
  central_bandB_V1_valid.positive_of_eq (by norm_num) rfl (by push_cast; exact hx)
/-- The polynomial `centralBandV (107/200) bandB_Cplus bandB_D` for `bandB_sides`,
expanded in powers of `u`, on `[15/56, 9/28]`. -/
def central_bandB_V2 : Arithmetic.BernsteinRow :=
  { interval := ⟨(15/56),(9/28)⟩
    polynomial := [(4789/40000), (-166767/200000), (15211/20000), (594767/200000), (-35211/40000)]
    degree := 4
    coefficients := [(1401939853/393379840000), (1357056667/245862400000), (4327610183/491724800000), (1657823819/122931200000), (2414995853/122931200000)] }

theorem central_bandB_V2_valid : central_bandB_V2.Valid (1401939853/786759680000) :=
  Arithmetic.BernsteinRow.valid_of_check (by decide +kernel)
theorem central_bandB_V2_positive {x : ℝ} (hx : ((15/56) : ℝ) ≤ x ∧ x ≤ (9/28)) :
    0 < central_bandB_V2.polynomial.eval x :=
  central_bandB_V2_valid.positive_of_eq (by norm_num) rfl (by push_cast; exact hx)
/-- The polynomial `centralBandV (107/200) bandB_Cplus bandB_D` for `bandB_sides`,
expanded in powers of `u`, on `[9/28, 3/7]`. -/
def central_bandB_V3 : Arithmetic.BernsteinRow :=
  { interval := ⟨(9/28),(3/7)⟩
    polynomial := [(4789/40000), (-166767/200000), (15211/20000), (594767/200000), (-35211/40000)]
    degree := 4
    coefficients := [(2414995853/122931200000), (3929339921/122931200000), (771085879/15366400000), (287583337/3841600000), (1277993/12005000)] }

theorem central_bandB_V3_valid : central_bandB_V3.Valid (2414995853/245862400000) :=
  Arithmetic.BernsteinRow.valid_of_check (by decide +kernel)
theorem central_bandB_V3_positive {x : ℝ} (hx : ((9/28) : ℝ) ≤ x ∧ x ≤ (3/7)) :
    0 < central_bandB_V3.polynomial.eval x :=
  central_bandB_V3_valid.positive_of_eq (by norm_num) rfl (by push_cast; exact hx)
end SquaresInCircles.Eight.Generated
