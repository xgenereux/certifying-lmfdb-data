import CertifyingLmfdbData.Polynomial.AllRoots
import CertifyingLmfdbData.Regulator.RegulatorBound
import CertifyingLmfdbData.Regulator.MatrixPerturbation
import CertifyingLmfdbData.IntervalArithmetic.DyadicReal
import CertifyingLmfdbData.SexticExampleHyp
import CertifyingLmfdbData.SexticExampleUnits

noncomputable section

open DegSix

abbrev n : ℕ := 6
abbrev m : ℕ := 4
abbrev f := DegSix.myPoly
abbrev u := fundUnits
abbrev α : Fin 4 → ℂ := ![uniqueRootNear_rroot1.root,
                       uniqueRootNear_rroot2.root,
                       uniqueRootNear_rroot3.root,
                       uniqueRootNear_croot1.root]
abbrev t : Fin 4 → ℕ := ![1, 1, 1, 2]
abbrev bound_matrix := Matrix.of fun i j ↦ t j * Real.log ‖(u i).aeval (α j)‖
abbrev bound := |bound_matrix.det|

abbrev α_approx : Fin 4 → ℂ := ![toComplex (approxRoots 0),
                                 toComplex (approxRoots 1),
                                 toComplex (approxRoots 2),
                                 toComplex (approxRoots 4)]

abbrev embedding_matrix_components : Fin 2 → Matrix (Fin 4) (Fin 4) ℝ :=
  ![
    !![1.2469796037174670610500097680084796212645494617928042107311,
       -1.8019377358048382524722046390148901023318383242637143001071,
       -1.8019377358048382524722046390148901023318383242637143001071,
       -0.44504186791262880857780512899358951893271113752908991062398;
       2.2469796037174670610500097680084796212645494617928042107311,
       -0.80193773580483825247220463901489010233183832426371430010713,
       -0.80193773580483825247220463901489010233183832426371430010713,
       0.55495813208737119142219487100641048106728886247091008937602;
       -7.2369110744810749202764784562430485133747976818110634233160,
       5.2918504230486113322236761863413204414485067408101945317954,
       -0.084099479829258322334857630281760032121153443755337331366929,
       -0.10991626417474238284438974201282096213457772494182017875205;
       -7.5448896028509790506486635592409793731775370824891693019609,
       0.24293308352630601870146177931795071785211895475367602095721,
       -5.1330168193515636358570720373051297557175412298118558422052,
       -0.75302039628253293894999023199152037873545053820719578926890],
    !![0, 0, 0, 0;
       0, 0, 0, 0;
       0, 0, 0, -1.1112596539906122701949371368842592933284122257078292519541;
       0, 0, 0, -1.1112596539906122701949371368842592933284122257078292519541]
  ]

open Complex in
abbrev embedding_matrix_complex : Matrix (Fin 4) (Fin 4) ℂ :=
    Matrix.of fun i j ↦ embedding_matrix_components 0 i j + embedding_matrix_components 1 i j * I

abbrev bound_matrix_approx := Matrix.of fun i j ↦
  t j * Real.log √(embedding_matrix_components 0 i j ^ 2 + embedding_matrix_components 1 i j ^ 2)
abbrev bound_approx := |bound_matrix_approx.det|

-- AI generated
theorem det_fin_four_scratch (A : Matrix (Fin 4) (Fin 4) ℝ) :
    A.det =
      A 0 0 * (A.submatrix (Fin.succAbove 0) (Fin.succAbove 0)).det
      - A 0 1 * (A.submatrix (Fin.succAbove 0) (Fin.succAbove 1)).det
      + A 0 2 * (A.submatrix (Fin.succAbove 0) (Fin.succAbove 2)).det
      - A 0 3 * (A.submatrix (Fin.succAbove 0) (Fin.succAbove 3)).det := by
  rw [Matrix.det_succ_row A 0]
  simp [Fin.sum_univ_four]
  ring

-- AI generated, not reviewed
theorem log_bound {x y : ℂ} {ε : ℝ}
    (hεx : ε < ‖y‖) (hxy : ‖x - y‖ ≤ ε) :
    |Real.log ‖x‖ - Real.log ‖y‖| ≤ Real.log (‖y‖ / (‖y‖ - ε)) := by
  have hε_nonneg : 0 ≤ ε := (norm_nonneg (x - y)).trans hxy
  have hy_pos : 0 < ‖y‖ := lt_of_le_of_lt hε_nonneg hεx
  have hy_sub_pos : 0 < ‖y‖ - ε := sub_pos.mpr hεx
  have hx_lower : ‖y‖ - ε ≤ ‖x‖ := by
    have : ‖y‖ - ‖x‖ ≤ ε := by
      calc
        ‖y‖ - ‖x‖ ≤ ‖y - x‖ := norm_sub_norm_le y x
        _ = ‖x - y‖ := by rw [norm_sub_rev]
        _ ≤ ε := hxy
    linarith
  have hx_pos : 0 < ‖x‖ := hy_sub_pos.trans_le hx_lower
  have hx_upper : ‖x‖ ≤ ‖y‖ + ε := by
    have : ‖x‖ - ‖y‖ ≤ ε := (norm_sub_norm_le x y).trans hxy
    linarith
  have hy_add_pos : 0 < ‖y‖ + ε := by positivity
  have hright :
      Real.log (‖y‖ / (‖y‖ - ε)) = Real.log ‖y‖ - Real.log (‖y‖ - ε) := by
    rw [Real.log_div hy_pos.ne' hy_sub_pos.ne']
  have hupper :
      Real.log ‖x‖ - Real.log ‖y‖ ≤ Real.log (‖y‖ / (‖y‖ - ε)) := by
    have hleft :
        Real.log (‖y‖ + ε) - Real.log ‖y‖ = Real.log ((‖y‖ + ε) / ‖y‖) := by
      rw [Real.log_div hy_add_pos.ne' hy_pos.ne']
    have hratio : (‖y‖ + ε) / ‖y‖ ≤ ‖y‖ / (‖y‖ - ε) := by
      rw [div_le_div_iff₀ hy_pos hy_sub_pos]
      nlinarith [sq_nonneg ε]
    calc
      Real.log ‖x‖ - Real.log ‖y‖ ≤ Real.log (‖y‖ + ε) - Real.log ‖y‖ :=
        sub_le_sub_right (Real.log_le_log hx_pos hx_upper) _
      _ = Real.log ((‖y‖ + ε) / ‖y‖) := hleft
      _ ≤ Real.log (‖y‖ / (‖y‖ - ε)) :=
        Real.log_le_log (div_pos hy_add_pos hy_pos) hratio
  have hlower :
      Real.log ‖y‖ - Real.log ‖x‖ ≤ Real.log (‖y‖ / (‖y‖ - ε)) := by
    rw [hright]
    exact sub_le_sub_left (Real.log_le_log hy_sub_pos hx_lower) _
  exact abs_le.mpr ⟨by linarith, hupper⟩

theorem matrix_entry_diffs'' (i j) :
    ‖(u i).aeval (α_approx j) - embedding_matrix_complex i j‖ ≤ 1e-55 := by
  simp [approxRoots, α_approx, rroot1, rroot2, rroot3, croot1,
        fundUnits, fundU1, fundU2, fundU3, fundU4,
        Complex.norm_eq_sqrt_sq_add_sq]
  fin_cases i <;> simp <;> fin_cases j <;>
    simp <;> ring_nf <;>
    simp [Complex.I_pow_eq_pow_mod'] <;> ring_nf <;>
    dyadic_interval [approx := 400]

theorem matrix_entry_diffs (i j) :
    |bound_matrix i j - bound_matrix_approx i j| ≤ 2 * 1e-53 := by
  calc
    _ = |(t j : ℝ)| * |Real.log ‖(u i).aeval (α j)‖ - Real.log ‖embedding_matrix_complex i j‖| := by
      rw [← abs_mul, mul_sub]
      simp [Complex.norm_eq_sqrt_sq_add_sq]
    _ ≤ 2 * |Real.log ‖(u i).aeval (α j)‖ - Real.log ‖embedding_matrix_complex i j‖| := by
      gcongr
      fin_cases j <;> simp
    _ ≤ 2 * 1e-53 := by
      gcongr
      have : ‖(Polynomial.aeval (α j)) (u i) - embedding_matrix_complex i j‖ ≤ 2 * 1e-55 := by
        grw [norm_sub_le_norm_sub_add_norm_sub, matrix_entry_diffs'', two_mul]
        gcongr
        fin_cases j <;> convert! sigma_bounds_uniform _ i <;> simp [uniqueRoots]
      grw [log_bound _ this] <;>
        simp [Complex.norm_eq_sqrt_sq_add_sq] <;>
        fin_cases i <;> fin_cases j <;>
          simp only [Fin.reduceFinMk, Matrix.cons_val] <;>
          dyadic_interval [approx := 1000] -- high precision needed for log bound

theorem bound_diff : |bound - bound_approx| ≤ 1e-48 := by
  grw [abs_abs_sub_abs_le, ← Real.norm_eq_abs,
      absolute_bound_frob' bound_matrix_approx bound_matrix
        (Matrix.of fun i j ↦ 2 * 1e-53) matrix_entry_diffs]
  simp [Fin.sum_univ_castSucc]
  ring_nf
  simp [← one_div]
  dyadic_interval [approx := 400]

theorem bound_det : 1e-48 < bound_matrix_approx.det := by
  simp_rw [det_fin_four_scratch, Matrix.det_fin_three]
  simp [bound_matrix_approx, Fin.succAbove, Complex.norm_eq_sqrt_sq_add_sq]
  dyadic_interval [approx := 50]

theorem bound_approx_estimate : |bound_approx - 15.959695183485| ≤ 1e-12 := by
  have hpos : 0 < bound_matrix_approx.det := by
    grw [← bound_det]
    positivity
  rw [bound_approx, abs_of_pos hpos]
  simp_rw [det_fin_four_scratch, Matrix.det_fin_three]
  simp [bound_matrix_approx, Fin.succAbove, Complex.norm_eq_sqrt_sq_add_sq, abs_le]
  constructor <;> dyadic_interval [approx := 100]

theorem bound_estimate : |bound - 15.959695183485| ≤ 2 * 1e-12 := by
  grw [abs_sub_le, bound_diff, bound_approx_estimate]
  dyadic_interval [approx := 50]

-- `Fact (Irreducible f)` comes from `CertifyingLmfdbData.SexticExampleHyp`
theorem bound_regulator : ∃ k : ℕ, 1 ≤ k ∧ bound = k • NumberField.Units.regulator (AdjoinRoot f) := by
  refine regulator_le_regOfFamily_comp
    (m := m) (f := f) (u := u) (α := α) (t := t) (bound := bound)
    ?_ (fun i ↦ ?_) (fun i ↦ ?_) (fun i j ↦ ?_) (fun i ↦ ?_) (fun i ↦ ?_) (fun hc ↦ ?_) ?_
  · unfold NumberField.Units.rank
    rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
    change m = (NumberField.InfinitePlace.nrRealPlaces SexticExample.K ) +
    (NumberField.InfinitePlace.nrComplexPlaces SexticExample.K)  -1
    rw [SexticExample.nrComplexPlaces_eq, SexticExample.nrRealPlaces_eq]
  · fin_cases i <;>
      simp [uniqueRootNear_rroot1.isRoot,
            uniqueRootNear_rroot2.isRoot,
            uniqueRootNear_rroot3.isRoot,
            uniqueRootNear_croot1.isRoot]
  · fin_cases i <;>
      simp [rroot1_im_zero, rroot2_im_zero, rroot3_im_zero, zero_lt_croot4_im.le]
  · fin_cases i <;>
      fin_cases j <;>
        intros hij <;>
        apply UniqueRootNear.distinct <;>
        simp_all [rroot1, rroot2, rroot3, croot1] <;>
        norm_num
  · fin_cases i <;>
      simp [rroot1_im_zero, rroot2_im_zero, rroot3_im_zero, zero_lt_croot4_im.ne.symm]
  · fin_cases i
    · use unit1_isIntegral
      exact unit1_isUnit''
    · use unit2_isIntegral
      exact unit2_isUnit''
    · use unit3_isIntegral
      exact unit3_isUnit''
    · use unit4_isIntegral
      exact unit4_isUnit''
  · have := bound_diff
    rw [hc, zero_sub, abs_neg] at this
    replace := le_of_abs_le this
    apply this.not_gt
    rw [bound_approx, lt_abs]
    left
    exact bound_det
  · rfl

theorem regulator_aux : ∃ m : ℕ, 1 ≤ m ∧
    15.959695183485 ∈ Set.Icc ((1 - 1e-12) * m • NumberField.Units.regulator (AdjoinRoot f))
      ((1 + 1e-12) * m • NumberField.Units.regulator (AdjoinRoot f)) := by
  obtain ⟨m, hm, hb⟩ := bound_regulator
  refine ⟨m, hm, ?_⟩
  rw [← hb]
  have key := bound_estimate
  rw [abs_le] at key
  apply key.symm.imp
  · intro h
    rw [sub_le_iff_le_add] at h
    grw [h]
    norm_num
  · intro h
    rw [le_sub_iff_add_le] at h
    grw [← h]
    norm_num

end

-- Higher precision embedding matrix approximation:
-- open Complex in
-- abbrev embedding_matrix_complex : Matrix (Fin 4) (Fin 4) ℂ :=
--   Matrix.transpose !![1.24697960371746706105000976800847962126454946179280421073109887819370730491297456915188501465317074333411618441834908601827145851077314552166879576913,
--   2.24697960371746706105000976800847962126454946179280421073109887819370730491297456915188501465317074333411618441834908601827145851077314552166879576913,
--   -7.23691107448107492027647845624304851337479768181106342331598004804758207318270186974716483803087250830439017746403890061074105576612909322430347095481,
--   -7.54488960285097905064866355924097937317753708248916930196090713805903230421263266244611771816155585227277973736469093585378140450574307668854460475799;
--   -1.80193773580483825247220463901489010233183832426371430010712484639886484085587993100272290943702483063662192873735020727958326576116027450757872534144,
--   -0.801937735804838252472204639014890102331838324263714300107124846398864840855879931002722909437024830636621928737350207279583265761160274507578725341442,
--   5.29185042304861133222367618634132044144850674081019453179542876141245457589707102224731092774904716073963397678627287250392732191207602996352028047393,
--   0.242933083526306018701461779317950717852118954753676020957205036819882430128216522092703003658851586768895863630573579206072597640142609934272759363362;
--   -1.80193773580483825247220463901489010233183832426371430010712484639886484085587993100272290943702483063662192873735020727958326576116027450757872534144,
--   -0.801937735804838252472204639014890102331838324263714300107124846398864840855879931002722909437024830636621928737350207279583265761160274507578725341442,
--   -0.0840994798292583223348576302817600321211534437553373313669293758169952124735512982364192900009478381931462618368720433855942588674349319332053791081638,
--   -5.13301681935156363585707203730512975571754122981185584220515310040956735824240579839102721409114341216388437499257133668344898313936835196245290021873;
--   -0.445041867912628808577805128993589518932711137529089910623974031794842464057094638149162105216145912697494255680998878738688192749612871014090070427686,
--   0.554958132087371191422194871006410481067288862470910089376025968205157535942905361850837894783854087302505744319001121261311807250387128985909929572314,
--   -0.109916264174742382844389742012820962134577724941820178752051936410315071885810723701675789567708174605011488638002242522623614500774257971819859144628 - 1.11125965399061227019493713688425929332841222570782925195411577478364402073486916579704326163360786475083493787567870098942925601085463604350900373616*I,
--   -0.753020396282532938949990231991520378735450538207195789268901121806292695087025430848114985346829256665883815581650913981728541489226854478331204230872 - 1.11125965399061227019493713688425929332841222570782925195411577478364402073486916579704326163360786475083493787567870098942925601085463604350900373616*I]
