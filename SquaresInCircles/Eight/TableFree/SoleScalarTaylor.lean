module

public import SquaresInCircles.Eight.TableFree.SoleScalarRadicals
public import SquaresInCircles.Eight.TableFree.BoundedRadicalPerturbation

/-!
# Whole-interval Taylor error for the sole-E scalars

Uncompiled source. All comparisons use the same parameter t in the
same coefficient family. Four anchor rows and one optional tilt row
are handled uniformly; the absent fifth row has weight zero. Each
weighted radical loses at most 500 times the Taylor remainder, and
the outside term loses at most 100 times that remainder.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.SoleScalarTaylor
open SoleECoefficients SoleScalarData HighOrderTaylor BoundedRadicalPerturbation
open SoleScalarPolynomials (ScalarCase band atG isDE negativeIndex)

theorem input_bounds {t : ℝ} (ht : t∈Set.Icc 0 frameCap) :
    Real.sin t∈Set.Icc 0 1 ∧ Real.cos t∈Set.Icc 0 (1001/1000) ∧
    S15 t∈Set.Icc 0 1 ∧ C16 t∈Set.Icc 0 (1001/1000) := by
  rcases frame_remainders ht with ⟨hs0,hs1,hc0,hc1⟩
  have hc := (transport_trig ht).1
  have hs := (transport_trig ht).2.2.1
  have hcu := Real.cos_le_one t
  have hsu := Real.sin_le_one t
  have he : remainder≤1/1000 := by norm_num [remainder]
  exact ⟨⟨hs,hsu⟩,⟨by linarith,by linarith⟩,
    ⟨S15_nonneg ht,by linarith⟩,⟨by linarith,by linarith⟩⟩

theorem input_errors {t : ℝ} (ht : t∈Set.Icc 0 frameCap) :
    |Real.sin t-S15 t|≤remainder ∧ |Real.cos t-C16 t|≤remainder ∧
    |Real.sin (t/2)-S15 (t/2)|≤remainder := by
  rcases frame_remainders ht with ⟨hs0,hs1,hc0,hc1⟩
  have hh : t/2∈Set.Icc 0 frameCap :=
    ⟨by linarith [ht.1],by linarith [ht.1,ht.2]⟩
  rcases frame_remainders hh with ⟨hh0,hh1,_,_⟩
  refine ⟨?_,?_,?_⟩
  · rw [abs_of_nonneg hs0]; exact hs1.le
  · rw [abs_sub_comm,abs_of_nonneg hc0]; exact hc1.le
  · rw [abs_of_nonneg hh0]; exact hh1.le

theorem tilted_bounds {K v sn cs : ℝ}
    (hK : K∈Set.Icc 0 (11/10)) (hv : v∈Set.Icc 0 (7/10))
    (hs : sn∈Set.Icc 0 1) (hc : cs∈Set.Icc 0 (1001/1000)) :
    K*(cs+v*sn)∈Set.Icc 0 2 := by
  have hvs := mul_nonneg hv.1 hs.1
  have hvu := mul_le_mul_of_nonneg_left hs.2 hv.1
  have hinner : cs+v*sn≤1701/1000 := by linarith [hc.2,hv.2]
  have hh := mul_le_mul_of_nonneg_left hinner hK.1
  exact ⟨mul_nonneg hK.1 (add_nonneg hc.1 hvs),by nlinarith [hK.2]⟩

theorem tilted_error {K v t : ℝ} (ht : t∈Set.Icc 0 frameCap)
    (hK : K∈Set.Icc 0 (11/10)) (hv : v∈Set.Icc 0 (7/10)) :
    |K*(Real.cos t+v*Real.sin t)-K*(C16 t+v*S15 t)|≤2*remainder := by
  have he := input_errors ht
  have hKv0 := mul_nonneg hK.1 hv.1
  have hKv1 : K*v≤77/100 := by
    nlinarith [mul_le_mul hK.2 hv.2 hv.1 (by norm_num : (0:ℝ)≤11/10)]
  have hh := linear_difference
    (show |K|≤11/10 by rwa [abs_of_nonneg hK.1])
    (show |K*v|≤77/100 by rwa [abs_of_nonneg hKv0]) he.2.1 he.1
  have hid : K*(Real.cos t+v*Real.sin t)-K*(C16 t+v*S15 t)=
      (K*Real.cos t+(K*v)*Real.sin t)-(K*C16 t+(K*v)*S15 t) := by ring
  rw [hid]
  nlinarith [show 0≤remainder by norm_num [remainder]]

theorem coordinate_errors (s : ScalarCase) {t : ℝ} (ht : t∈domain (band s))
    (i : Fin 4) :
    |firstData s t (Real.sin t) (Real.cos t) i-firstData s t (S15 t) (C16 t) i|≤
        3*remainder ∧
    |secondData s t (Real.sin t) (Real.cos t) i-secondData s t (S15 t) (C16 t) i|≤
        3*remainder := by
  have hd := angle ht
  rcases coefficient_bounds ht with ⟨hk,hk1,hl,hl1,hc,hc1,hg,hg1,he,he1⟩
  have hn := tilted_error hd ⟨hk.le,hk1.le⟩ ⟨hg,by linarith⟩
  have hr := tilted_error hd (by norm_num : (1:ℝ)∈Set.Icc 0 (11/10))
    (by norm_num : (7/10:ℝ)∈Set.Icc 0 (7/10))
  have hp := tilted_error hd (by norm_num : (1:ℝ)∈Set.Icc 0 (11/10))
    ⟨he,by linarith⟩
  change |nData (band s) t (Real.sin t) (Real.cos t)-
    nData (band s) t (S15 t) (C16 t)|≤2*remainder at hn
  simp only [one_mul] at hr hp
  have hpn : |pData (band s) t (Real.sin t) (Real.cos t)-
      pData (band s) t (S15 t) (C16 t)|≤2*remainder := by
    dsimp [pData]
    split_ifs
    · norm_num [remainder]
    · exact hp
  change |rData (Real.sin t) (Real.cos t)-rData (S15 t) (C16 t)|≤2*remainder at hr
  have hr0 : 0≤remainder := by norm_num [remainder]
  fin_cases i <;> simp [firstData,secondData] <;> split_ifs <;>
    simp only [sub_self,abs_zero] <;> (repeat' constructor) <;> linarith

theorem nu_bounds (s : ScalarCase) {t sn cs : ℝ}
    (ht : t∈domain (band s)) (hs : sn∈Set.Icc 0 1)
    (hco : cs∈Set.Icc 0 (1001/1000)) :
    nuData s t sn cs∈Set.Icc 0 2 := by
  rcases coefficient_bounds ht with ⟨hk,hk1,hl,hl1,hc,hc1,hg,hg1,he,he1⟩
  have hn := tilted_bounds ⟨hk.le,hk1.le⟩ (show g (band s) t∈Set.Icc 0 (7/10)
    from ⟨hg,by linarith⟩) hs hco
  have hr := tilted_bounds (by norm_num : (1:ℝ)∈Set.Icc 0 (11/10))
    (by norm_num : (7/10:ℝ)∈Set.Icc 0 (7/10)) hs hco
  change nData (band s) t sn cs∈Set.Icc 0 2 at hn
  simp only [one_mul] at hr
  change rData sn cs∈Set.Icc 0 2 at hr
  generalize hj : negativeIndex s=j
  fin_cases j <;> simp [nuData,hj] <;> split_ifs <;>
    constructor <;> linarith [hn.1,hn.2,hr.1,hr.2]

theorem nu_error (s : ScalarCase) {t : ℝ} (ht : t∈domain (band s)) :
    |nuData s t (Real.sin t) (Real.cos t)-nuData s t (S15 t) (C16 t)|≤3*remainder := by
  rcases coefficient_bounds ht with ⟨hk,hk1,hl,hl1,hc,hc1,hg,hg1,he,he1⟩
  have hn := tilted_error (angle ht) ⟨hk.le,hk1.le⟩ ⟨hg,by linarith⟩
  have hr := tilted_error (angle ht) (by norm_num : (1:ℝ)∈Set.Icc 0 (11/10))
    (by norm_num : (7/10:ℝ)∈Set.Icc 0 (7/10))
  change |nData (band s) t (Real.sin t) (Real.cos t)-
    nData (band s) t (S15 t) (C16 t)|≤2*remainder at hn
  simp only [one_mul] at hr
  change |rData (Real.sin t) (Real.cos t)-rData (S15 t) (C16 t)|≤2*remainder at hr
  generalize hj : negativeIndex s=j
  fin_cases j <;> simp [nuData,hj] <;> split_ifs <;>
    simp only [sub_self,abs_zero] <;>
    linarith [show 0≤remainder by norm_num [remainder]]

theorem weight_error (s : ScalarCase) {t : ℝ} (ht : t∈domain (band s))
    (i : Fin 5) :
    |weightData s t (Real.sin t) i-weightData s t (S15 t) i|≤3*remainder := by
  have hs := (input_errors (angle ht)).1
  have hk := (coefficient_bounds ht).1
  have hku := (coefficient_bounds ht).2.1
  have hh := constant_product_difference
    (show |k (band s) t|≤11/10 by rw [abs_of_nonneg hk.le]; exact hku.le) hs
  dsimp [weightData]
  split_ifs <;> simp only [sub_self,abs_zero] <;>
    nlinarith [show 0≤remainder by norm_num [remainder]]

theorem square_error (s : ScalarCase) {t : ℝ} (ht : t∈domain (band s))
    (i : Fin 5) :
    |squareData s t (Real.sin t) (Real.cos t) i-squareData s t (S15 t) (C16 t) i|≤
      100*remainder := by
  rcases input_bounds (angle ht) with ⟨hs,hc,hs',hc'⟩
  have he := input_errors (angle ht)
  have he0 : 0≤remainder := by norm_num [remainder]
  dsimp [squareData]
  split_ifs with hi hg haux
  · let j : Fin 4 := ⟨i.val,hi⟩
    have hb := coordinates_bounds s ht hs hc j
    have hb' := coordinates_bounds s ht hs' hc' j
    have hd := coordinate_errors s ht j
    have ha : |firstData s t (Real.sin t) (Real.cos t) j|≤2 := by
      rwa [abs_of_nonneg hb.1]
    have ha' : |firstData s t (S15 t) (C16 t) j|≤2 := by
      rwa [abs_of_nonneg hb'.1]
    have hbb : |secondData s t (Real.sin t) (Real.cos t) j|≤2 := by
      rwa [abs_of_nonneg hb.2.2.1]
    have hbb' : |secondData s t (S15 t) (C16 t) j|≤2 := by
      rwa [abs_of_nonneg hb'.2.2.1]
    change |squaredData s t (Real.sin t) (Real.cos t) j-
      squaredData s t (S15 t) (C16 t) j|≤100*remainder
    unfold squaredData
    split_ifs
    · exact negative_pair_difference he0 ha ha' hbb hbb'
        (by rwa [abs_of_nonneg hs'.1]) hd.1 hd.2 he.1
    · simpa only [sub_zero] using positive_pair_difference he0 ha ha' hbb hbb' hd.1 hd.2
  · norm_num [remainder]
  · norm_num [remainder]
  · norm_num [remainder]

theorem row_error (s : ScalarCase) {t : ℝ} (ht : t∈domain (band s))
    (i : Fin 5) :
    |weightData s t (Real.sin t) i*Real.sqrt (squareData s t (Real.sin t) (Real.cos t) i)-
      weightData s t (S15 t) i*Real.sqrt (squareData s t (S15 t) (C16 t) i)|≤
        500*remainder := by
  rcases input_bounds (angle ht) with ⟨hs,hc,hs',hc'⟩
  have hp := SoleScalarPolynomials.square_bounds s i (SoleScalarPolynomials.local_parameter ht)
  rw [(polynomial_rows s i t).1] at hp
  exact weighted_root_difference (square_nonneg s ht hs hc i) hp.1.le hp.2.le
    (by norm_num [remainder]) (by norm_num [remainder])
    (weight_bounds s ht hs i) (weight_bounds s ht hs' i)
    (square_error s ht i) (weight_error s ht i)

theorem rowSum_error (s : ScalarCase) {t : ℝ} (ht : t∈domain (band s)) :
    rowSum s t (Real.sin t) (Real.cos t)≤taylorSum s t+2500*remainder := by
  have hh (i : Fin 5) :
      weightData s t (Real.sin t) i*Real.sqrt (squareData s t (Real.sin t) (Real.cos t) i)≤
        weightData s t (S15 t) i*Real.sqrt (squareData s t (S15 t) (C16 t) i)+500*remainder := by
    have hi := (le_abs_self _).trans (row_error s ht i)
    linarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hh i)
  simpa [rowSum,taylorSum,Finset.sum_add_distrib] using hsum

end SquaresInCircles.Eight.TableFree.SoleScalarTaylor
