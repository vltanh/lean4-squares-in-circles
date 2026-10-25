module

public import SquaresInCircles.Eight.Owners.CenteredMonomialBounds

/-!
# Eight squares: weights and circle masses of the negative capture

Each band is one interval of the total sine (`Band`, `domain`). The two stress weights `a` and `f`
are fixed before the reduction to the four geometric vertices; only the auxiliary circle masses
`mass b j` depend on the vertex. Their bounds on each band follow from the coefficients of
translated cubics (`weight_bounds`, `mass_lower`, `mass_positive`).
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.NegativeCaptureData
open CenteredMonomialBounds

inductive Band where
  | low | high
  deriving DecidableEq

instance : Fintype Band where
  elems := {.low, .high}
  complete x := by cases x <;> decide

def lo : Band → ℚ | .low => 1499/100000 | .high => 7/50
def hi : Band → ℚ | .low => 7/50 | .high => 27/100
def mid : Band → ℚ | .low => 15499/200000 | .high => 41/200
def rad : Band → ℚ | .low => 12501/200000 | .high => 13/200
def domain (b : Band) : Set ℝ := Icc (lo b:ℝ) (hi b:ℝ)

def cubic (a b c d : ℚ) : ℚ[X] := C a+C b*X+C c*X^2+C d*X^3

def weight : Band → Fin 2 → ℚ[X]
  | .low => ![
      cubic (58266015/100000000) (49799768/100000000)
        (1791176/100000000) (1988864/100000000),
      cubic (116228301/100000000) (-98466323/100000000)
        (67559020/100000000) (-53098860/100000000)]
  | .high => ![
      cubic (54399682/100000000) (106786562/100000000)
        (-239861499/100000000) (124305637/100000000),
      cubic (118077884/100000000) (-124066546/100000000)
        (171820838/100000000) (-157930403/100000000)]

def aP (b : Band) : ℚ[X] := weight b 0
def fP (b : Band) : ℚ[X] := weight b 1
def a (b : Band) (s : ℝ) : ℝ := aeval s (aP b)
def f (b : Band) (s : ℝ) : ℝ := aeval s (fP b)

def massARot : Band → ℚ[X]
  | .low => cubic (29321190/100000000) (-6437836/100000000)
      (-8548820/100000000) (-2487824/100000000)
  | .high => cubic (28814817/100000000) (1328081/100000000)
      (-44460217/100000000) (29999321/100000000)
def massAFixed : Band → ℚ[X]
  | .low => cubic (29321149/100000000) (6383697/100000000)
      (2230447/100000000) (5344/100000000)
  | .high => cubic (28783482/100000000) (14208751/100000000)
      (-29930677/100000000) (11781294/100000000)
def massAShort : Band → ℚ[X]
  | .low => cubic (29128247/100000000) (6262238/100000000)
      (2265742/100000000) (92/100000000)
  | .high => cubic (28599173/100000000) (13958462/100000000)
      (-29326945/100000000) (11390367/100000000)
def massBFixed : Band → ℚ[X]
  | .low => cubic (29244531/100000000) (6335186/100000000)
      (2244512/100000000) (3228/100000000)
  | .high => cubic (28710297/100000000) (14108777/100000000)
      (-29689570/100000000) (11625249/100000000)
def massBShift : Band → ℚ[X]
  | .low => cubic (29434761/100000000) (-6184228/100000000)
      (-8551134/100000000) (-2485409/100000000)
  | .high => cubic (28923047/100000000) (1661368/100000000)
      (-44810167/100000000) (30220724/100000000)
def massD : Band → ℚ[X]
  | .low => cubic (38742819/100000000) (-18856981/100000000)
      (16249805/100000000) (-12349400/100000000)
  | .high => cubic (39080192/100000000) (-23548383/100000000)
      (35513119/100000000) (-32128996/100000000)
def massHFixed : Band → ℚ[X]
  | .low => cubic (38742971/100000000) (-12988701/100000000)
      (3634484/100000000) (-2886230/100000000)
  | .high => cubic (39095601/100000000) (-17973189/100000000)
      (24832696/100000000) (-27086828/100000000)
def massHSec : Band → ℚ[X]
  | .low => cubic (38742821/100000000) (-12977080/100000000)
      (11595495/100000000) (2435946/100000000)
  | .high => cubic (39075678/100000000) (-17590352/100000000)
      (30393360/100000000) (-16369759/100000000)
def massHShort : Band → ℚ[X]
  | .low => cubic (38744825/100000000) (-12988079/100000000)
      (3634516/100000000) (-2886114/100000000)
  | .high => cubic (39097437/100000000) (-17972312/100000000)
      (24831665/100000000) (-27085564/100000000)
def massE : Band → ℚ[X]
  | .low => cubic (30376027/100000000) (-24055072/100000000)
      (17155095/100000000) (-13228033/100000000)
  | .high => cubic (30824754/100000000) (-30272741/100000000)
      (42529811/100000000) (-38889082/100000000)

/-- The circle masses at the vertex `j`. The fifth entry is `massE b`, whose mass on the circle of E
is `s` times it. -/
def mass (b : Band) (j : Fin 4) : Fin 5 → ℚ[X] := ![
  if j=0 then massARot b else if j=2 then massAShort b else massAFixed b,
  if j=0 ∨ j=1 then massBFixed b else massBShift b,
  massD b,
  if j=1 then massHSec b else if j=3 then massHShort b else massHFixed b,
  massE b]

def Q : ℚ := 1957767069/500000000
def eta : ℚ := 3/500
def k : ℚ := 307/1000
def K : ℚ := 13/12
def shortAngle : ℚ := 3/200
def sigma : ℚ := 14999437506/1000000000000
def chi : ℚ := 999887502109/1000000000000
def delta (j : Fin 4) : ℚ := if j=0 ∨ j=1 then 0 else 1/100000000

def weightLower : Fin 2 → ℚ := ![58/100,93/100]
def weightUpper : Fin 2 → ℚ := ![69/100,117/100]
def massLower : Fin 5 → ℚ := ![26/100,26/100,34/100,35/100,24/100]

/-! The translated coefficients of a cubic, in closed form. -/

private lemma r28_translated_cubic (m a b c d : ℚ) :
    translated m (cubic a b c d)=
      cubic (a+b*m+c*m^2+d*m^3) (b+2*c*m+3*d*m^2) (c+3*d*m) d := by
  apply Polynomial.funext
  intro x
  simp only [translated,cubic,eval_comp,eval_add,eval_mul,eval_pow,eval_C,eval_X]
  ring

private lemma r28_cubic_coeff (a b c d : ℚ) :
    (cubic a b c d).coeff 0=a ∧ (cubic a b c d).coeff 1=b ∧
      (cubic a b c d).coeff 2=c ∧ (cubic a b c d).coeff 3=d := by
  simp [cubic,coeff_X,coeff_C,coeff_X_pow]

private lemma r28_series_cubic (a b c d : ℚ) : series 3 (cubic a b c d)=cubic a b c d := by
  obtain ⟨h0,h1,h2,h3⟩ := r28_cubic_coeff a b c d
  simp only [series,Fin.sum_univ_three,Fin.val_zero,Fin.val_one,Fin.val_two,h0]
  norm_num [h1,h2,h3]
  simp only [cubic]
  ring

private lemma r28_series_translated (m a b c d : ℚ) :
    translated m (cubic a b c d)=series 3 (translated m (cubic a b c d)) := by
  rw [r28_translated_cubic,r28_series_cubic]

private lemma r28_lowerOn_cubic (m r a b c d : ℚ) :
    lowerOn 3 m r (cubic a b c d)=(a+b*m+c*m^2+d*m^3)-|b+2*c*m+3*d*m^2| * r+
      min (c+3*d*m) 0*r^2-|d| * r^3 := by
  obtain ⟨h0,h1,h2,h3⟩ := r28_cubic_coeff (a+b*m+c*m^2+d*m^3) (b+2*c*m+3*d*m^2) (c+3*d*m) d
  simp only [lowerOn,lower,r28_translated_cubic,Fin.sum_univ_three,Fin.val_zero,Fin.val_one,
    Fin.val_two,h0]
  norm_num [h1,h2,h3,lowerTerm]
  ring

private lemma r28_neg_cubic (a b c d : ℚ) : -cubic a b c d=cubic (-a) (-b) (-c) (-d) := by
  simp only [cubic,map_neg]
  ring

private lemma r28_neg_shift_cubic (a b c d e : ℚ) :
    -(cubic a b c d+C e*X)=cubic (-a) (-b-e) (-c) (-d) := by
  simp only [cubic,map_neg,map_sub]
  ring

theorem domain_centered {b : Band} {s : ℝ} (hs : s∈domain b) :
    |s-(mid b:ℝ)|≤(rad b:ℝ) := by
  cases b <;> dsimp [domain,lo,hi,mid,rad] at hs ⊢ <;>
    apply abs_le.mpr <;> constructor <;> linarith [hs.1,hs.2]

theorem domain_full {b : Band} {s : ℝ} (hs : s∈domain b) :
    s∈Icc (1499/100000 : ℝ) (27/100) := by
  cases b <;> dsimp [domain,lo,hi] at hs ⊢ <;>
    constructor <;> linarith [hs.1,hs.2]

theorem domain_covers {s : ℝ} (hs : s∈Icc (1499/100000:ℝ) (27/100)) :
    ∃b, s∈domain b := by
  by_cases h : s≤7/50
  · exact ⟨.low,by norm_num [lo]; linarith [hs.1],by norm_num [hi]; linarith⟩
  · exact ⟨.high,by norm_num [lo]; linarith,by norm_num [hi]; linarith [hs.2]⟩

theorem weight_series : ∀b i,
    translated (mid b) (weight b i)=series 3 (translated (mid b) (weight b i)) ∧
    translated (mid b) (-weight b i)=series 3 (translated (mid b) (-weight b i)) := by
  intro b i
  cases b <;> fin_cases i <;>
    simp only [weight,Fin.zero_eta,Fin.mk_one,Matrix.cons_val_zero,Matrix.cons_val_one,
      r28_neg_cubic] <;>
    exact ⟨r28_series_translated _ _ _ _ _,r28_series_translated _ _ _ _ _⟩

theorem weight_coefficients : ∀b i,
    weightLower i<lowerOn 3 (mid b) (rad b) (weight b i) ∧
    -weightUpper i<lowerOn 3 (mid b) (rad b) (-weight b i) := by
  intro b i
  cases b <;> fin_cases i <;>
    simp only [weight,Fin.zero_eta,Fin.mk_one,Matrix.cons_val_zero,Matrix.cons_val_one,
      r28_neg_cubic,r28_lowerOn_cubic,weightLower,weightUpper,mid,rad] <;>
    norm_num [abs_eq_max_neg,max_def,min_def]

theorem shifted_weight_series : ∀b,
    translated (mid b) (-(fP b+C k*X))=
      series 3 (translated (mid b) (-(fP b+C k*X))) := by
  intro b
  cases b <;>
    simp only [fP,weight,Matrix.cons_val_one,Matrix.cons_val_zero,r28_neg_shift_cubic] <;>
    exact r28_series_translated _ _ _ _ _

theorem shifted_weight_coefficients : ∀b,
    (-117/100:ℚ)<lowerOn 3 (mid b) (rad b) (-(fP b+C k*X)) := by
  intro b
  cases b <;>
    simp only [fP,weight,Matrix.cons_val_one,Matrix.cons_val_zero,r28_neg_shift_cubic,
      r28_lowerOn_cubic,mid,rad,k] <;>
    norm_num [abs_eq_max_neg,max_def,min_def]

theorem mass_series : ∀b j i,
    translated (mid b) (mass b j i)=series 3 (translated (mid b) (mass b j i)) := by
  intro b j i
  fin_cases i <;> simp only [mass,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Matrix.cons_val,
    Matrix.cons_val_zero,Matrix.cons_val_one] <;> (try split_ifs) <;> cases b <;>
    exact r28_series_translated _ _ _ _ _

theorem mass_coefficients : ∀b j i,
    massLower i<lowerOn 3 (mid b) (rad b) (mass b j i) := by
  intro b j i
  fin_cases i <;> simp only [mass,massLower,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,
    Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one] <;>
    (try split_ifs) <;> cases b <;>
    simp only [massARot,massAFixed,massAShort,massBFixed,massBShift,massD,massHFixed,
      massHSec,massHShort,massE,r28_lowerOn_cubic,mid,rad] <;>
    norm_num [abs_eq_max_neg,max_def,min_def]

theorem weight_bounds {b : Band} {s : ℝ} (hs : s∈domain b) (i : Fin 2) :
    (weightLower i:ℝ)<aeval s (weight b i) ∧
      aeval s (weight b i)<(weightUpper i:ℝ) := by
  have hr : 0≤rad b := by cases b <;> norm_num [rad]
  have hlo := interval_lower (weight_series b i).1 hr (domain_centered hs)
  have hhi := interval_lower (weight_series b i).2 hr (domain_centered hs)
  have hnumlo : (weightLower i:ℝ)<(lowerOn 3 (mid b) (rad b) (weight b i):ℝ) := by
    exact_mod_cast (weight_coefficients b i).1
  have hnumhi : -(weightUpper i:ℝ)<(lowerOn 3 (mid b) (rad b) (-weight b i):ℝ) := by
    exact_mod_cast (weight_coefficients b i).2
  rw [map_neg] at hhi
  exact ⟨hnumlo.trans_le hlo,by linarith⟩

theorem actual_weight_bounds {b : Band} {s : ℝ} (hs : s∈domain b) :
    58/100<a b s ∧ a b s<69/100 ∧ 93/100<f b s ∧ f b s<117/100 := by
  have h0 := weight_bounds hs 0
  have h1 := weight_bounds hs 1
  simpa [a,f,aP,fP,weightLower,weightUpper] using
    And.intro h0.1 (And.intro h0.2 h1)

theorem shifted_weight_upper {b : Band} {s : ℝ} (hs : s∈domain b) :
    f b s+(307/1000)*s<117/100 := by
  have hr : 0≤rad b := by cases b <;> norm_num [rad]
  have hh := interval_lower (shifted_weight_series b) hr (domain_centered hs)
  have hn : (-117/100:ℝ)<
      (lowerOn 3 (mid b) (rad b) (-(fP b+C k*X)):ℝ) := by
    exact_mod_cast shifted_weight_coefficients b
  simp only [map_neg,map_add,map_mul,aeval_C,aeval_X,eq_ratCast] at hh
  have hk : ((k:ℚ):ℝ)=307/1000 := by norm_num [k]
  rw [hk] at hh
  dsimp [f]
  linarith

theorem mass_lower {b : Band} {s : ℝ} (hs : s∈domain b)
    (j : Fin 4) (i : Fin 5) : (massLower i:ℝ)<aeval s (mass b j i) := by
  have hr : 0≤rad b := by cases b <;> norm_num [rad]
  have hh := interval_lower (mass_series b j i) hr (domain_centered hs)
  have hn : (massLower i:ℝ)<(lowerOn 3 (mid b) (rad b) (mass b j i):ℝ) := by
    exact_mod_cast mass_coefficients b j i
  exact hn.trans_le hh

theorem mass_positive {b : Band} {s : ℝ} (hs : s∈domain b)
    (j : Fin 4) (i : Fin 5) : 0<aeval s (mass b j i) := by
  have hh := mass_lower hs j i
  have hn : (0:ℝ)< massLower i := by fin_cases i <;> norm_num [massLower]
  exact hn.trans hh

end SquaresInCircles.Eight.NegativeCaptureData
