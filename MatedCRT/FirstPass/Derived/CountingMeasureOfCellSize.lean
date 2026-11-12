import MatedCRT.FirstPass.Derived.CellDiamLowerOfVolumeGrowth

/-!
# Convergence of the counting measure from the cell size estimate

Lemma 2.9 (BG20 Lemma A.4): with polynomially high probability, for every `D ⊆ B_ρ` and every
nonnegative, bounded, Lipschitz `f`, the sum `∑_{a ∈ V^ε(D)} f(w_a)` is `ε⁻¹ ∫_D f dμ_h` up to the
thickening of `D` and an error `ε^{-1+α}`. We follow the proof of BG20 (Appendix A): each cell has
`μ_h`-mass `ε` and two cells meet in a `μ_h`-null set (area parametrization), the cells meeting `B_ρ`
have diameter at most `ε^q` (the upper half of Lemma 2.8), and their number is `O(ε^{-1-q/4})`.
For the last point BG20 uses a tail estimate of the LQG mass of `B_{ρ+ε^q}`; we use instead the
coverage estimate `P[𝔻 ⊄ η([-M, M])] = O(M^{-c})` of the mating-of-trees coupling, which bounds the
`μ_h`-mass of the unit disk by `2M`.

* `IsAreaParametrized.measure_image_Icc_inter`: pieces of `η` over intervals with disjoint interiors
  meet in a `μ`-null set;
* `IsAreaParametrized.counting_bounds`: the deterministic two-sided bound;
* `countingMeasureConvergenceStmt_of_cellSize`: `CountingMeasureConvergenceStmt` from
  `CellSizeEstimateStmt`.
-/

open Set Metric MeasureTheory Filter Topology HarmonicBalls

namespace MatedCRT

section Deterministic

variable {μ : Measure ℂ} {η : ℝ → ℂ}

/-- The `μ`-mass of `η([b, c])` is at most `c - b`, also for `b = c`. -/
theorem IsAreaParametrized.measure_image_Icc_le (hpar : IsAreaParametrized μ η) {b c : ℝ}
    (hbc : b ≤ c) : μ (η '' Icc b c) ≤ ENNReal.ofReal (c - b) := by
  refine ENNReal.le_of_forall_pos_le_add fun t ht _ => ?_
  calc μ (η '' Icc b c) ≤ μ (η '' Icc b (c + t)) :=
        measure_mono (image_mono (Icc_subset_Icc le_rfl (by have := t.2; linarith)))
    _ = ENNReal.ofReal (c + t - b) := hpar.2.2.2 _ _ (by have : (0 : ℝ) < t := ht; linarith)
    _ = ENNReal.ofReal (c - b) + t := by
        rw [show c + (t : ℝ) - b = (c - b) + t by ring, ENNReal.ofReal_add (by linarith) (NNReal.coe_nonneg t),
          ENNReal.ofReal_coe_nnreal]

/-- Pieces of an area-parametrized curve over intervals with disjoint interiors meet in a `μ`-null
set. -/
theorem IsAreaParametrized.measure_image_Icc_inter (hpar : IsAreaParametrized μ η) {a b c d : ℝ}
    (hab : a < b) (hbc : b ≤ c) (hcd : c < d) : μ (η '' Icc a b ∩ η '' Icc c d) = 0 := by
  set A := η '' Icc a b
  set C := η '' Icc c d
  have hC : MeasurableSet C := (isCompact_Icc.image hpar.1).isClosed.measurableSet
  have hsub : η '' Icc a d ⊆ (A ∪ C) ∪ η '' Icc b c := by
    rintro _ ⟨t, ⟨hat, htd⟩, rfl⟩
    rcases le_or_gt t b with htb | hbt
    · exact Or.inl (Or.inl ⟨t, ⟨hat, htb⟩, rfl⟩)
    rcases le_or_gt c t with hct | htc
    · exact Or.inl (Or.inr ⟨t, ⟨hct, htd⟩, rfl⟩)
    · exact Or.inr ⟨t, ⟨hbt.le, htc.le⟩, rfl⟩
  have h1 : ENNReal.ofReal (d - a) ≤ μ (A ∪ C) + ENNReal.ofReal (c - b) := by
    rw [← hpar.2.2.2 a d (by linarith)]
    exact (measure_mono hsub).trans
      ((measure_union_le _ _).trans (add_le_add le_rfl (hpar.measure_image_Icc_le hbc)))
  have h2 : μ (A ∪ C) + μ (A ∩ C) = μ A + μ C := measure_union_add_inter A hC
  rw [hpar.2.2.2 a b hab, hpar.2.2.2 c d hcd] at h2
  have hsplit : ENNReal.ofReal (d - a) =
      ENNReal.ofReal (b - a) + ENNReal.ofReal (d - c) + ENNReal.ofReal (c - b) := by
    rw [← ENNReal.ofReal_add (by linarith) (by linarith),
      ← ENNReal.ofReal_add (by linarith) (by linarith)]
    congr 1
    ring
  rw [hsplit] at h1
  have h3 : ENNReal.ofReal (b - a) + ENNReal.ofReal (d - c) ≤ μ (A ∪ C) :=
    (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 h1
  have hfin : μ (A ∪ C) ≠ ⊤ :=
    ne_top_of_le_ne_top (b := ENNReal.ofReal (b - a) + ENNReal.ofReal (d - c)) (by finiteness)
      (h2 ▸ le_self_add)
  have h4 : μ (A ∪ C) + μ (A ∩ C) ≤ μ (A ∪ C) + 0 := by rw [add_zero, h2]; exact h3
  exact le_antisymm ((ENNReal.add_le_add_iff_left hfin).1 h4) zero_le

/-- Each cell has `μ`-mass `ε`. -/
theorem IsAreaParametrized.measure_cell (hpar : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε)
    (k : ℤ) : μ (cell ε η k) = ENNReal.ofReal ε := by
  rw [cell, hpar.2.2.2 _ _ (by nlinarith)]
  congr 1
  ring

/-- Two distinct cells meet in a `μ`-null set. -/
theorem IsAreaParametrized.measure_cell_inter (hpar : IsAreaParametrized μ η) {ε : ℝ}
    (hε : 0 < ε) {j k : ℤ} (hjk : j ≠ k) : μ (cell ε η j ∩ cell ε η k) = 0 := by
  have key : ∀ j k : ℤ, j < k → μ (cell ε η j ∩ cell ε η k) = 0 := by
    intro j k h
    have h' : (j : ℝ) ≤ k - 1 := by
      have : j ≤ k - 1 := by omega
      exact_mod_cast this
    exact hpar.measure_image_Icc_inter (by nlinarith) (by nlinarith) (by nlinarith)
  rcases lt_or_gt_of_ne hjk with h | h
  · exact key j k h
  · rw [inter_comm]
    exact key k j h

theorem isCompact_cell (hη : Continuous η) (ε : ℝ) (k : ℤ) : IsCompact (cell ε η k) :=
  isCompact_Icc.image hη

/-- The cells cover the plane. -/
theorem exists_mem_cell (hsurj : Function.Surjective η) {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    ∃ k : ℤ, z ∈ cell ε η k := by
  obtain ⟨t, rfl⟩ := hsurj z
  refine ⟨⌈t / ε⌉, t, ⟨?_, ?_⟩, rfl⟩
  · have h := Int.ceil_lt_add_one (t / ε)
    have : ((⌈t / ε⌉ : ℤ) : ℝ) - 1 < t / ε := by linarith
    rw [lt_div_iff₀ hε] at this
    linarith
  · have h := Int.le_ceil (t / ε)
    rw [div_le_iff₀ hε] at h
    linarith

/-- A cell contained in `η([-M, M])` has its time interval meeting `(-M, M)`. -/
theorem IsAreaParametrized.cell_index_bounds (hpar : IsAreaParametrized μ η) {ε M : ℝ}
    (hε : 0 < ε) (hM : 0 < M) {k : ℤ} (hk : cell ε η k ⊆ η '' Icc (-M) M) :
    -M < ε * k ∧ ε * (k - 1) < M := by
  have hpos : μ (cell ε η k) ≠ 0 := by
    rw [hpar.measure_cell hε]
    exact (ENNReal.ofReal_pos.2 hε).ne'
  have hinter : cell ε η k ∩ η '' Icc (-M) M = cell ε η k := inter_eq_left.2 hk
  constructor
  · by_contra hle
    rw [not_lt] at hle
    exact hpos (hinter ▸ hpar.measure_image_Icc_inter (by nlinarith) hle (by linarith))
  · by_contra hle
    rw [not_lt] at hle
    rw [← hinter, inter_comm] at hpos
    exact hpos (hpar.measure_image_Icc_inter (by linarith) hle (by nlinarith))

/-- The integral over a finite union of measurable sets which pairwise meet in null sets is the sum
of the integrals. -/
theorem setIntegral_biUnion_finset_of_measure_inter {X ι : Type*} [MeasurableSpace X]
    {μ : Measure X} [DecidableEq ι] (t : Finset ι) {s : ι → Set X} {f : X → ℝ}
    (hs : ∀ i ∈ t, MeasurableSet (s i)) (hst : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → μ (s i ∩ s j) = 0)
    (hf : ∀ i ∈ t, IntegrableOn f (s i) μ) :
    ∫ x in ⋃ i ∈ t, s i, f x ∂μ = ∑ i ∈ t, ∫ x in s i, f x ∂μ := by
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t hat IH =>
    have hs' : ∀ i ∈ t, MeasurableSet (s i) := fun i hi => hs i (Finset.mem_insert_of_mem hi)
    have hf' : ∀ i ∈ t, IntegrableOn f (s i) μ := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hdisj : AEDisjoint μ (s a) (⋃ i ∈ t, s i) := by
      show μ (s a ∩ ⋃ i ∈ t, s i) = 0
      rw [inter_iUnion₂]
      refine le_antisymm ((measure_biUnion_finset_le t _).trans ?_) zero_le
      rw [Finset.sum_eq_zero fun i hi => hst a (Finset.mem_insert_self a t) i
        (Finset.mem_insert_of_mem hi) fun h => hat (h ▸ hi)]
    rw [Finset.set_biUnion_insert, setIntegral_union₀ hdisj
      (Finset.measurableSet_biUnion t hs').nullMeasurableSet (hf a (Finset.mem_insert_self a t))
      (integrableOn_finset_iUnion.2 hf'), Finset.sum_insert hat,
      IH hs' (fun i hi j hj => hst i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)) hf']

/-- **Deterministic counting bound** (BG20, proof of Lemma A.4). Let `η` be parametrized by
`μ`-area with `B_1 ⊆ η([-M, M])`, and let every cell meeting `B_ρ` have diameter at most `s`, where
`s < a` and `ρ + a ≤ 1`. For `D ⊆ B_ρ`, `f` nonnegative, bounded by `L` and `L`-Lipschitz on the
thickening `B_a(D)`, and points `w_k ∈ H^ε_k ∩ cl(D)`, the sum `∑_{k ∈ V^ε(D)} f(w_k)` lies between
`ε⁻¹ ∫_D f dμ` and `ε⁻¹ ∫_{B_a(D)} f dμ` up to `(2M/ε + 5) L s`. -/
theorem IsAreaParametrized.counting_bounds (hpar : IsAreaParametrized μ η) {ε M ρ a s L : ℝ}
    (hε : 0 < ε) (hM : 0 < M) (hs : 0 ≤ s) (hsa : s < a) (hρa : ρ + a ≤ 1) (hL : 0 ≤ L)
    (hcov : ball (0 : ℂ) 1 ⊆ η '' Icc (-M) M)
    (hdiam : ∀ k : ℤ, (cell ε η k ∩ ball 0 ρ).Nonempty → diam (cell ε η k) ≤ s)
    {D : Set ℂ} {f : ℂ → ℝ} {w : ℤ → ℂ} (hD : D ⊆ ball 0 ρ)
    (hfb : ∀ x ∈ thickening a D, 0 ≤ f x ∧ |f x| ≤ L)
    (hfL : ∀ x ∈ thickening a D, ∀ y ∈ thickening a D, |f x - f y| ≤ L * ‖x - y‖)
    (hw : ∀ k ∈ cellVertices ε η D, w k ∈ cell ε η k ∩ closure D) :
    ε⁻¹ * ∫ x in D, f x ∂μ - (2 * M / ε + 5) * (L * s) ≤ ∑' k : cellVertices ε η D, f (w k) ∧
    ∑' k : cellVertices ε η D, f (w k) ≤
      ε⁻¹ * ∫ x in thickening a D, f x ∂μ + (2 * M / ε + 5) * (L * s) := by
  classical
  set T := thickening a D with hT
  set V := cellVertices ε η D with hV
  have hbdd : ∀ k, Bornology.IsBounded (cell ε η k) := fun k => (isCompact_cell hpar.1 ε k).isBounded
  have hcellm : ∀ k, MeasurableSet (cell ε η k) := fun k =>
    (isCompact_cell hpar.1 ε k).isClosed.measurableSet
  have hdiamV : ∀ k ∈ V, diam (cell ε η k) ≤ s := by
    rintro k ⟨y, hyc, hyD⟩
    exact hdiam k ⟨y, hyc, hD hyD⟩
  have hcellT : ∀ k ∈ V, cell ε η k ⊆ T := by
    intro k hk x hx
    obtain ⟨y, hyc, hyD⟩ := hk
    exact mem_thickening_iff.2 ⟨y, hyD, (dist_le_diam_of_mem (hbdd k) hx hyc).trans_lt
      ((hdiamV k ⟨y, hyc, hyD⟩).trans_lt hsa)⟩
  have hT1 : T ⊆ ball 0 1 := by
    intro x hx
    obtain ⟨y, hyD, hxy⟩ := mem_thickening_iff.1 hx
    have hy := mem_ball_zero_iff.1 (hD hyD)
    rw [mem_ball_zero_iff]
    have h1 := norm_sub_norm_le x y
    rw [dist_eq_norm] at hxy
    linarith
  -- the cells of `V` are finitely many
  set N : ℕ := ⌈M / ε⌉₊ + 1 with hN
  have hVN : ∀ k ∈ V, k ∈ Finset.Icc (-(N : ℤ)) N := by
    intro k hk
    have hb := hpar.cell_index_bounds hε hM ((hcellT k hk).trans (hT1.trans hcov))
    have hc := Nat.le_ceil (M / ε)
    have h1 : -(M / ε) < k := by
      rw [neg_div', div_lt_iff₀ hε]
      linarith
    have h2 : (k : ℝ) - 1 < M / ε := by
      rw [lt_div_iff₀ hε]
      linarith
    have h3 : -((N : ℤ) : ℝ) < k := by push_cast [hN]; linarith
    have h4 : (k : ℝ) < (N : ℤ) + 1 := by push_cast [hN]; linarith
    rw [Finset.mem_Icc]
    constructor
    · exact_mod_cast h3.le
    · have : k < (N : ℤ) + 1 := by exact_mod_cast h4
      omega
  have hfin : V.Finite := (Finset.Icc (-(N : ℤ)) N).finite_toSet.subset fun k hk => hVN k hk
  set F := hfin.toFinset with hF
  have hmemF : ∀ k, k ∈ F ↔ k ∈ V := fun k => hfin.mem_toFinset
  have hcard : (F.card : ℝ) ≤ 2 * M / ε + 5 := by
    have h1 : F.card ≤ (Finset.Icc (-(N : ℤ)) N).card :=
      Finset.card_le_card fun k hk => hVN k ((hmemF k).1 hk)
    rw [Int.card_Icc] at h1
    have h2 : ((N : ℤ) + 1 - -(N : ℤ)).toNat = 2 * N + 1 := by omega
    rw [h2] at h1
    have h3 : (N : ℝ) ≤ M / ε + 2 := by
      rw [hN]
      push_cast
      linarith [Nat.ceil_lt_add_one (div_nonneg hM.le hε.le)]
    have h4 : (F.card : ℝ) ≤ 2 * N + 1 := by exact_mod_cast h1
    have h5 : 2 * (M / ε) = 2 * M / ε := by ring
    linarith
  have hsum : ∑' k : V, f (w k) = ∑ k ∈ F, f (w k) := by
    rw [tsum_subtype V (fun k => f (w k)), tsum_eq_sum (s := F)]
    · exact Finset.sum_congr rfl fun k hk => indicator_of_mem ((hmemF k).1 hk) _
    · intro k hk
      exact indicator_of_notMem (fun h => hk ((hmemF k).2 h)) _
  -- integrability on the thickening
  have hLip : LipschitzOnWith (Real.toNNReal L) f T := LipschitzOnWith.of_dist_le_mul
    fun x hx y hy => by
      rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hL]
      exact hfL x hx y hy
  have hTm : MeasurableSet T := isOpen_thickening.measurableSet
  have hμT : μ T ≠ ⊤ := ne_top_of_le_ne_top (b := ENNReal.ofReal (M - -M)) ENNReal.ofReal_ne_top
    ((measure_mono (hT1.trans hcov)).trans_eq (hpar.2.2.2 _ _ (by linarith)))
  have hintT : IntegrableOn f T μ := by
    have : IsFiniteMeasure (μ.restrict T) := isFiniteMeasure_restrict.2 hμT
    exact Integrable.of_bound (hLip.continuousOn.aestronglyMeasurable hTm) L
      (ae_restrict_of_forall_mem hTm fun x hx => by rw [Real.norm_eq_abs]; exact (hfb x hx).2)
  have hintk : ∀ k ∈ V, IntegrableOn f (cell ε η k) μ := fun k hk => hintT.mono_set (hcellT k hk)
  -- the oscillation of `f` on a cell
  have hosc : ∀ k ∈ V, ∀ x ∈ cell ε η k, |f x - f (w k)| ≤ L * s := by
    intro k hk x hx
    have hwk := (hw k hk).1
    calc |f x - f (w k)| ≤ L * ‖x - w k‖ := hfL x (hcellT k hk hx) (w k) (hcellT k hk hwk)
      _ ≤ L * s := mul_le_mul_of_nonneg_left
          (((dist_eq_norm x (w k)) ▸ dist_le_diam_of_mem (hbdd k) hx hwk).trans (hdiamV k hk)) hL
  have hreal : ∀ k, μ.real (cell ε η k) = ε := fun k => by
    rw [measureReal_def, hpar.measure_cell hε, ENNReal.toReal_ofReal hε.le]
  have hfin_k : ∀ k, μ (cell ε η k) ≠ ⊤ := fun k => by
    rw [hpar.measure_cell hε]
    exact ENNReal.ofReal_ne_top
  have hcellup : ∀ k ∈ V, f (w k) ≤ ε⁻¹ * ∫ x in cell ε η k, f x ∂μ + L * s := by
    intro k hk
    have h := setIntegral_mono_on (integrableOn_const (hfin_k k)) (hintk k hk) (hcellm k)
      fun x hx => (show f (w k) - L * s ≤ f x by linarith [(abs_le.1 (hosc k hk x hx)).1])
    rw [setIntegral_const, smul_eq_mul, hreal] at h
    have := mul_le_mul_of_nonneg_left h (inv_nonneg.2 hε.le)
    rw [← mul_assoc, inv_mul_cancel₀ hε.ne', one_mul] at this
    linarith
  have hcelllo : ∀ k ∈ V, ε⁻¹ * ∫ x in cell ε η k, f x ∂μ ≤ f (w k) + L * s := by
    intro k hk
    have h := setIntegral_mono_on (hintk k hk) (integrableOn_const (hfin_k k)) (hcellm k)
      fun x hx => (show f x ≤ f (w k) + L * s by linarith [(abs_le.1 (hosc k hk x hx)).2])
    rw [setIntegral_const, smul_eq_mul, hreal] at h
    have := mul_le_mul_of_nonneg_left h (inv_nonneg.2 hε.le)
    rwa [← mul_assoc, inv_mul_cancel₀ hε.ne', one_mul] at this
  -- the union of the cells of `V`
  set U := ⋃ k ∈ F, cell ε η k with hU
  have hUm : MeasurableSet U := Finset.measurableSet_biUnion F fun k _ => hcellm k
  have hUT : U ⊆ T := iUnion₂_subset fun k hk => hcellT k ((hmemF k).1 hk)
  have hDU : D ⊆ U := by
    intro z hz
    obtain ⟨k, hk⟩ := exists_mem_cell hpar.2.2.1 hε z
    exact mem_iUnion₂.2 ⟨k, (hmemF k).2 ⟨z, hk, hz⟩, hk⟩
  have hintU : IntegrableOn f U μ := hintT.mono_set hUT
  have hnnU : 0 ≤ᵐ[μ.restrict U] f := ae_restrict_of_forall_mem hUm fun x hx => (hfb x (hUT hx)).1
  have hnnT : 0 ≤ᵐ[μ.restrict T] f := ae_restrict_of_forall_mem hTm fun x hx => (hfb x hx).1
  have hDUi : ∫ x in D, f x ∂μ ≤ ∫ x in U, f x ∂μ := setIntegral_mono_set hintU hnnU hDU.eventuallyLE
  have hUTi : ∫ x in U, f x ∂μ ≤ ∫ x in T, f x ∂μ := setIntegral_mono_set hintT hnnT hUT.eventuallyLE
  have hUsum : ∫ x in U, f x ∂μ = ∑ k ∈ F, ∫ x in cell ε η k, f x ∂μ :=
    setIntegral_biUnion_finset_of_measure_inter F (fun k _ => hcellm k)
      (fun i _ j _ hij => hpar.measure_cell_inter hε hij) fun k hk => hintk k ((hmemF k).1 hk)
  have hLs : 0 ≤ L * s := mul_nonneg hL hs
  have herr : (F.card : ℝ) * (L * s) ≤ (2 * M / ε + 5) * (L * s) :=
    mul_le_mul_of_nonneg_right hcard hLs
  have hinv := inv_nonneg.2 hε.le
  rw [hsum]
  constructor
  · have h1 : ε⁻¹ * ∫ x in U, f x ∂μ ≤ ∑ k ∈ F, (f (w k) + L * s) := by
      rw [hUsum, Finset.mul_sum]
      exact Finset.sum_le_sum fun k hk => hcelllo k ((hmemF k).1 hk)
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at h1
    have h2 := mul_le_mul_of_nonneg_left hDUi hinv
    linarith
  · have h1 : ∑ k ∈ F, f (w k) ≤ ∑ k ∈ F, (ε⁻¹ * ∫ x in cell ε η k, f x ∂μ + L * s) :=
      Finset.sum_le_sum fun k hk => hcellup k ((hmemF k).1 hk)
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, ← hUsum] at h1
    have h2 := mul_le_mul_of_nonneg_left hUTi hinv
    linarith

end Deterministic

/-- **Lemma 2.9 from Lemma 2.8** (BG20 Lemma A.4): `CountingMeasureConvergenceStmt` holds for every
space-filling SLE model for which the cell size estimate `CellSizeEstimateStmt` holds; only its upper
half is used. The exponents are `α = β = q/4` with `q = 1/(2+γ)²`; the number of cells meeting `B_ρ`
is controlled by the coverage estimate of the mating-of-trees coupling with `M = ε^{-q/4}`. -/
theorem countingMeasureConvergenceStmt_of_cellSize {𝒮 : SpaceFillingSLEModel}
    (hcell : CellSizeEstimateStmt 𝒮) : CountingMeasureConvergenceStmt 𝒮 := by
  intro γ hγ hγ2
  set q : ℝ := 1 / (2 + γ) ^ 2 with hq_def
  have hq : 0 < q := by positivity
  have hq1 : q < 1 := by
    rw [hq_def, div_lt_one (by positivity)]
    nlinarith
  refine ⟨q / 4, q / 4, by positivity, by positivity, fun ρ hρ hρ1 Ω _ S hS => ?_⟩
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hMoT, hae⟩ := hS.matingOfTrees
  obtain ⟨c, hc, C, hcov⟩ := hMoT.coverage
  have hcovP : PolyHighProb S.P fun ε =>
      {ω | ball (0 : ℂ) 1 ⊆ η' ω '' Icc (-(ε ^ (-(q / 4)))) (ε ^ (-(q / 4)))} := by
    refine ⟨c * (q / 4), by positivity, C, 1, one_pos, fun ε hε hε1 => ?_⟩
    have hM : 1 < ε ^ (-(q / 4)) :=
      Real.one_lt_rpow_of_pos_of_lt_one_of_neg hε hε1 (by linarith)
    have h := hcov _ hM
    rw [← Real.rpow_mul hε.le, show -(q / 4) * -c = c * (q / 4) by ring] at h
    exact h
  have hexp : 2 / (2 + γ) ^ 2 - q = q := by rw [hq_def]; ring
  have hdiam := hcell γ hγ hγ2 q ρ hq hq1 hρ hρ1 Ω S hS
  have hW : ∀ᵐ ω ∂S.P, ω ∈ {ω | IsAreaParametrized (S.μ ω) (S.η ω) ∧ ⇑(η' ω) = S.η ω} :=
    hS.isAreaParametrized.and (hae.mono fun ω h => h.1)
  have hm0 : 0 < min (1 - ρ) (1 / 7 : ℝ) := lt_min (by linarith) (by norm_num)
  set ε₁ : ℝ := min 1 ((min (1 - ρ) (1 / 7 : ℝ)) ^ (4 / q)) with hε₁_def
  have hε₁ : 0 < ε₁ := lt_min one_pos (Real.rpow_pos_of_pos hm0 _)
  refine ((hdiam.inter hcovP).inter_ae hW).mono_of_small hε₁ fun ε hε hεε ω hω => ?_
  obtain ⟨⟨hdω, hcω⟩, hpar, hηω⟩ := hω
  simp only [mem_ofPred_eq] at hdω hcω
  rw [hηω] at hcω
  have hε1 : ε < 1 := hεε.trans_le (min_le_left _ _)
  have ht0 : 0 < ε ^ (q / 4) := Real.rpow_pos_of_pos hε _
  have ht : ε ^ (q / 4) < min (1 - ρ) (1 / 7 : ℝ) := by
    have h1 : ε ^ (q / 4) < ((min (1 - ρ) (1 / 7 : ℝ)) ^ (4 / q)) ^ (q / 4) :=
      Real.rpow_lt_rpow hε.le (hεε.trans_le (min_le_right _ _)) (by positivity)
    rwa [← Real.rpow_mul hm0.le, show 4 / q * (q / 4) = 1 by field_simp, Real.rpow_one] at h1
  have htρ : ε ^ (q / 4) < 1 - ρ := ht.trans_le (min_le_left _ _)
  have ht7 : ε ^ (q / 4) < 1 / 7 := ht.trans_le (min_le_right _ _)
  have hεq : ε ^ q = (ε ^ (q / 4)) ^ 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]
    norm_num
  have hεβ : ε ^ (-(q / 4)) = (ε ^ (q / 4))⁻¹ := Real.rpow_neg hε.le _
  have hεα : ε ^ (-1 + q / 4) = ε⁻¹ * ε ^ (q / 4) := by
    rw [Real.rpow_add hε, Real.rpow_neg_one]
  set t := ε ^ (q / 4) with ht_def
  intro D f w hD hfb hfL hw
  rw [hεβ] at hfb hfL hcω
  have hdiam' : ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 ρ).Nonempty → diam (cell ε (S.η ω) k) ≤ t ^ 4 :=
    fun k hk => by
      have h := (hdω k hk).2
      rwa [hexp, hεq] at h
  have ht4 : t ^ 4 < t := by
    have : t ^ 4 = t * t ^ 3 := by ring
    rw [this]
    have : t ^ 3 < 1 := pow_lt_one₀ ht0.le (by linarith) (by norm_num)
    nlinarith
  have key := hpar.counting_bounds hε (inv_pos.2 ht0) (by positivity) ht4 (by linarith)
    (inv_nonneg.2 ht0.le) hcω hdiam' hD hfb hfL hw
  have herr : (2 * t⁻¹ / ε + 5) * (t⁻¹ * t ^ 4) ≤ ε ^ (-1 + q / 4) := by
    rw [hεα]
    have h1 : (2 * t⁻¹ / ε + 5) * (t⁻¹ * t ^ 4) = ε⁻¹ * t * (2 * t + 5 * ε * t ^ 2) := by
      field_simp
    have h2 : 2 * t + 5 * ε * t ^ 2 ≤ 1 := by nlinarith
    rw [h1]
    calc ε⁻¹ * t * (2 * t + 5 * ε * t ^ 2) ≤ ε⁻¹ * t * 1 :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = ε⁻¹ * t := mul_one _
  constructor <;> linarith [key.1, key.2]

end MatedCRT
