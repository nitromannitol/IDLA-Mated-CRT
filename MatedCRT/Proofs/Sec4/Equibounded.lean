import MatedCRT.Draft.Section2
import MatedCRT.Draft.Section4
import MatedCRT.External.SLE
import MatedCRT.Proofs.Infra.Setting
import MatedCRT.Proofs.Infra.MatingOfTrees
import MatedCRT.Proofs.Infra.RandomWalk
import MatedCRT.Proofs.Sec4.ObstacleSpecialization

/-!
# Lemma 4.7: the rescaled odometers are equibounded along a deterministic subsequence

**Lemma 4.7** (lemma:equibounded, tex line 1740; proof lines 1747-1760). A.s., for each deterministic sequence
`ε_n → 0` there are a deterministic subsequence `𝓔` and a random constant `C` with `sup_{x ∈ B_ρ} |w̄^ε_t(x)| ≤ C`
for all `ε ∈ 𝓔` and all `t > 0`.

Proof (the paper's). By Lemma 4.3, `-q^ε_{B_ρ} ≤ w̃^ε_t ≤ 0` (eq:odometer-bounds). By Lemma 2.18 with `D = B_ρ`, with
polynomially high probability `q^ε_{B_ρ} ≤ C ε⁻¹ 𝓜(B_{ε^α}(B_ρ)) ≤ C ε⁻¹ sup_{D ⊆ B_{ρ'}} 𝓜(D)` with
`ρ' = (1 + ρ)/2`, and this supremum is a.s. finite by Lemma 2.17. By eq:meps-scaling (BG20 (1.8),
`MepsScalingInput`), `m_ε⁻¹ ≤ C' ε`. Along a subsequence with summable failure probabilities, the Borel-Cantelli
lemma gives `|w̄^ε_t| ≤ C' C sup_{D ⊆ B_{ρ'}} 𝓜(D)` for all but finitely many terms.

Two details left implicit in the paper:
* `w̄^ε_t(x) = m_ε⁻¹ w̃^ε_t(a^ε_x)`, where `a^ε_x` (`vertexOf`) may be a junk vertex outside `V^ε(cl(B_ρ))`; there
  `w̃^ε_t = 0` (`Equibounded.discreteLeastSupersolution_eq_zero_of_not_mem`: the infimum defining it is over a set
  unbounded below).
* The Borel-Cantelli lemma controls the terms after a random index only. Each of the finitely many earlier terms is
  bounded by `m_ε⁻¹ max q^ε_{B_ρ}`, finite since `V^ε(B_ρ) \ V^ε(∂B_ρ)` is a.s. finite (`η` continuous and proper).
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

namespace Equibounded

/-- A finitary sum decreases when its terms decrease and change at a single index only (if the supports are infinite,
both sums are `0`). -/
theorem finsum_le_finsum_of_eq_off {α : Type*} {f g : α → ℝ} (a : α) (hfg : ∀ x, f x ≤ g x)
    (hoff : ∀ x, x ≠ a → f x = g x) : ∑ᶠ x, f x ≤ ∑ᶠ x, g x := by
  have hsub : ∀ {f g : α → ℝ}, (∀ x, x ≠ a → f x = g x) →
      Function.support f ⊆ insert a (Function.support g) := fun {f g} h x hx => by
    by_cases hxa : x = a
    · exact Or.inl hxa
    · exact Or.inr (by rw [Function.mem_support, ← h x hxa]; exact hx)
  by_cases hg : (Function.support g).Finite
  · exact finsum_le_finsum ((hg.insert a).subset (hsub hoff)) hg hfg
  · have hf : ¬ (Function.support f).Finite := fun hf =>
      hg ((hf.insert a).subset (hsub fun x hx => (hoff x hx).symm))
    rw [finsum_of_infinite_support hf, finsum_of_infinite_support hg]

/-- Lowering `u` at the single vertex `a ≠ b` lowers the degree normalized Laplacian at `b`. -/
theorem mLaplacian_le_of_eq_off {α : Type*} (m : α → α → ℕ) {u v : α → ℝ} {a b : α} (hle : ∀ x, v x ≤ u x)
    (hoff : ∀ x, x ≠ a → v x = u x) (hb : b ≠ a) : mLaplacian m v b ≤ mLaplacian m u b := by
  unfold mLaplacian
  refine mul_le_mul_of_nonneg_left (finsum_le_finsum_of_eq_off a (fun x => ?_) (fun x hx => ?_))
    (inv_nonneg.2 (Nat.cast_nonneg _))
  · rw [hoff b hb]
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right (hle x) _) (Nat.cast_nonneg _)
  · rw [hoff b hb, hoff x hx]

/-- If every value `u(a)`, `u ∈ K`, can be lowered below any `c` inside `K`, then `sInf {u(a) : u ∈ K} = 0` (the
convention of `Real.sInf` for sets unbounded below and for the empty set). -/
theorem sInf_image_eval_eq_zero {α : Type*} {K : Set (α → ℝ)} (a : α)
    (h : ∀ u ∈ K, ∀ c : ℝ, ∃ v ∈ K, v a ≤ c) : sInf ((fun u : α → ℝ => u a) '' K) = 0 := by
  rcases K.eq_empty_or_nonempty with hK | ⟨u, hu⟩
  · rw [hK, Set.image_empty, Real.sInf_empty]
  · refine Real.sInf_of_not_bddBelow ?_
    rintro ⟨L, hL⟩
    obtain ⟨v, hv, hva⟩ := h u hu (L - 1)
    have hLv : L ≤ v a := hL ⟨v, hv, rfl⟩
    linarith

/-- Off `V ∪ W` the discrete least supersolution is `0`: the constraints do not bound `u(a)` from below there
(lowering `u` at `a` lowers `Δu` at the other vertices), so the infimum is over a set unbounded below (or empty). -/
theorem discreteLeastSupersolution_eq_zero_of_not_mem {α : Type*} {m : α → α → ℕ} {V W : Set α} {𝔯 φ : α → ℝ}
    {a : α} (haV : a ∉ V) (haW : a ∉ W) : discreteLeastSupersolution m V W 𝔯 φ a = 0 := by
  classical
  unfold discreteLeastSupersolution
  refine sInf_image_eval_eq_zero a fun u hu c => ?_
  rw [Set.mem_ofPred_eq] at hu
  obtain ⟨huV, huW⟩ := hu
  obtain ⟨v, hva, hvx⟩ : ∃ v : α → ℝ, v a = min (u a) c ∧ ∀ x, x ≠ a → v x = u x :=
    ⟨Function.update u a (min (u a) c), by simp, fun x hx => by simp [hx]⟩
  have hle : ∀ x, v x ≤ u x := fun x => by
    by_cases hx : x = a
    · rw [hx, hva]; exact min_le_left _ _
    · rw [hvx x hx]
  refine ⟨v, ?_, hva.trans_le (min_le_right _ _)⟩
  rw [Set.mem_ofPred_eq]
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · exact (mLaplacian_le_of_eq_off m hle hvx fun h => haV (h ▸ hb)).trans (huV b hb)
  · rw [hvx b fun h => haW (h ▸ hb)]
    exact huW b hb

/-- `V^ε(B_ρ) \ V^ε(∂B_ρ) ⊆ V^ε(cl(B_ρ))`. -/
theorem mem_cellVertices_closedBall_of_mem_ballInterior {ε ρ : ℝ} {η : ℝ → ℂ} {a : ℤ}
    (ha : a ∈ ballInterior ε η ρ) : a ∈ cellVertices ε η (closedBall 0 ρ) := by
  obtain ⟨z, hz, hzρ⟩ := (ha.1 : (cell ε η a ∩ ball (0 : ℂ) ρ).Nonempty)
  exact show (cell ε η a ∩ closedBall (0 : ℂ) ρ).Nonempty from ⟨z, hz, ball_subset_closedBall hzρ⟩

/-- eq:odometer-bounds at every vertex: if Lemma 4.3 holds and `q^ε_{B_ρ} ≤ B` on `V^ε(B_ρ) \ V^ε(∂B_ρ)`, then
`|w̃^ε_t| ≤ B` everywhere (`q^ε_{B_ρ} = 0` off `V^ε(B_ρ) \ V^ε(∂B_ρ)`, and `w̃^ε_t = 0` off `V^ε(cl(B_ρ))`). -/
theorem abs_matedLeastSupersolution_le {m : ℤ → ℤ → ℕ} {ε : ℝ} {η : ℝ → ℂ} {ρ t B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ a ∈ ballInterior ε η ρ, normExitTime m (ballInterior ε η ρ) a ≤ B)
    (h43 : ∀ a ∈ cellVertices ε η (closedBall 0 ρ),
      max (-normExitTime m (ballInterior ε η ρ) a) (matedObstacle m ε η ρ t a) ≤
          matedLeastSupersolution m ε η ρ t a ∧ matedLeastSupersolution m ε η ρ t a ≤ 0)
    (a : ℤ) : |matedLeastSupersolution m ε η ρ t a| ≤ B := by
  by_cases ha : a ∈ cellVertices ε η (closedBall 0 ρ)
  · obtain ⟨h1, h2⟩ := h43 a ha
    have h3 := (le_max_left _ _).trans h1
    rw [abs_of_nonpos h2]
    by_cases hb : a ∈ ballInterior ε η ρ
    · linarith [hB a hb]
    · rw [normExitTime_eq_zero_of_not_mem m hb] at h3
      linarith
  · unfold matedLeastSupersolution
    rw [discreteLeastSupersolution_eq_zero_of_not_mem
      (fun h => ha (mem_cellVertices_closedBall_of_mem_ballInterior h)) ha, abs_zero]
    exact hB0

/-- `|w̄^ε_t| ≤ |m_ε|⁻¹ B` if `|w̃^ε_t| ≤ B` (eq:discrete-scaling). -/
theorem abs_rescaledMatedLeastSupersolution_le {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {ρ t ε B : ℝ}
    {ω : Ω} (hw : ∀ a, |matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t a| ≤ B) (x : ℂ) :
    |rescaledMatedLeastSupersolution S ρ t ε ω x| ≤ |S.mε ε|⁻¹ * B := by
  unfold rescaledMatedLeastSupersolution rescale
  rw [abs_mul, abs_inv]
  exact mul_le_mul_of_nonneg_left (hw _) (inv_nonneg.2 (abs_nonneg _))

/-- The bound of the proof of Lemma 4.7 at one scale `ε`: on the event of Lemma 2.18 (its second part, used with
`D = B_ρ`), if `ε^α < ρ' - ρ`, Lemma 4.3 holds and `m_ε ≥ C_m⁻¹ ε⁻¹` (eq:meps-scaling), then
`|w̄^ε_t| ≤ C_m C sup_{D ⊆ B_{ρ'}} 𝓜(D)`. -/
theorem abs_rescaled_le_of_exitTime_bound {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {ρ ρ' α C Cm ε t : ℝ} {ω : Ω} (hε : 0 < ε) (hC : 0 < C) (hCm : 0 < Cm) (hmε : Cm⁻¹ * ε⁻¹ ≤ S.mε ε)
    (hεα : ε ^ α < ρ' - ρ)
    (hM : (⨆ (D : Set ℂ) (_ : D ⊆ ball 0 ρ'), largestExitTimeRV (S.μ ω) D) < ⊤)
    (hE : ∀ D : Set ℂ, D ⊆ ball 0 ρ → ∀ a ∈ cellVertices ε (S.η ω) D,
      ENNReal.ofReal (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) D) a) ≤
          expectedExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) D) a ∧
        expectedExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) D) a ≤
          ENNReal.ofReal (C * ε⁻¹) * largestExitTimeRV (S.μ ω) (thickening (ε ^ α) D))
    (h43 : ∀ a ∈ cellVertices ε (S.η ω) (closedBall 0 ρ),
      max (-normExitTime (S.mult ε ω) (ballInterior ε (S.η ω) ρ) a) (matedObstacle (S.mult ε ω) ε (S.η ω) ρ t a) ≤
          matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t a ∧
        matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t a ≤ 0) (x : ℂ) :
    |rescaledMatedLeastSupersolution S ρ t ε ω x| ≤
      Cm * C * (⨆ (D : Set ℂ) (_ : D ⊆ ball 0 ρ'), largestExitTimeRV (S.μ ω) D).toReal := by
  set M : ℝ≥0∞ := ⨆ (D : Set ℂ) (_ : D ⊆ ball 0 ρ'), largestExitTimeRV (S.μ ω) D with hMdef
  have hCε : 0 ≤ C * ε⁻¹ := mul_nonneg hC.le (inv_nonneg.2 hε.le)
  have hB0 : 0 ≤ C * ε⁻¹ * M.toReal := mul_nonneg hCε ENNReal.toReal_nonneg
  have hsub : thickening (ε ^ α) (ball (0 : ℂ) ρ) ⊆ ball 0 ρ' := by
    intro z hz
    obtain ⟨y, hy, hzy⟩ := mem_thickening_iff.1 hz
    rw [mem_ball] at hy ⊢
    linarith [dist_triangle z y 0]
  have hq : ∀ a ∈ ballInterior ε (S.η ω) ρ,
      normExitTime (S.mult ε ω) (ballInterior ε (S.η ω) ρ) a ≤ C * ε⁻¹ * M.toReal := by
    intro a ha
    obtain ⟨h1, h2⟩ := hE (ball 0 ρ) subset_rfl a ha.1
    have hle : ENNReal.ofReal (normExitTime (S.mult ε ω) (ballInterior ε (S.η ω) ρ) a) ≤
        ENNReal.ofReal (C * ε⁻¹ * M.toReal) := by
      calc ENNReal.ofReal (normExitTime (S.mult ε ω) (ballInterior ε (S.η ω) ρ) a)
          ≤ ENNReal.ofReal (C * ε⁻¹) * largestExitTimeRV (S.μ ω) (thickening (ε ^ α) (ball 0 ρ)) :=
            h1.trans h2
        _ ≤ ENNReal.ofReal (C * ε⁻¹) * M := by
            gcongr
            rw [hMdef]
            exact le_iSup₂_of_le (thickening (ε ^ α) (ball (0 : ℂ) ρ)) hsub le_rfl
        _ = ENNReal.ofReal (C * ε⁻¹ * M.toReal) := by
            rw [ENNReal.ofReal_mul hCε, ENNReal.ofReal_toReal hM.ne]
    exact (ENNReal.ofReal_le_ofReal_iff hB0).1 hle
  have hpos : 0 < Cm⁻¹ * ε⁻¹ := mul_pos (inv_pos.2 hCm) (inv_pos.2 hε)
  have hm0 : 0 < S.mε ε := hpos.trans_le hmε
  calc |rescaledMatedLeastSupersolution S ρ t ε ω x| ≤ |S.mε ε|⁻¹ * (C * ε⁻¹ * M.toReal) :=
        abs_rescaledMatedLeastSupersolution_le (abs_matedLeastSupersolution_le hB0 hq h43) x
    _ ≤ (Cm⁻¹ * ε⁻¹)⁻¹ * (C * ε⁻¹ * M.toReal) := by
        rw [abs_of_pos hm0]
        exact mul_le_mul_of_nonneg_right (inv_anti₀ hpos hmε) hB0
    _ = Cm * C * M.toReal := by
        rw [mul_inv, inv_inv, inv_inv]
        calc Cm * ε * (C * ε⁻¹ * M.toReal) = Cm * C * M.toReal * (ε * ε⁻¹) := by ring
          _ = Cm * C * M.toReal := by rw [mul_inv_cancel₀ hε.ne', mul_one]

/-- **Borel-Cantelli along a fast subsequence.** If `E r` holds with polynomially high probability as `r → 0` and
`ε_n → 0` (`ε_n > 0`), there is a strictly increasing `φ` with `ε_{φ(n)} < δ` such that a.s. `ω ∈ E (ε_{φ(n)})` for
all large `n`: `φ` is chosen with `ε_{φ(n)}^p ≤ 2^{-n}`, so that the failure probabilities are summable. -/
theorem exists_strictMono_ae_eventually_mem {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E : ℝ → Set Ω}
    (hE : PolyHighProb P E) {εs : ℕ → ℝ} (hεs : ∀ n, 0 < εs n) (hεs0 : Tendsto εs atTop (𝓝 0)) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ n, εs (φ n) < δ) ∧ ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ E (εs (φ n)) := by
  obtain ⟨p, hp, C, r₀, hr₀, hPE⟩ := hE
  have hc : ∀ n : ℕ, 0 < min (min δ r₀) (((1 / 2 : ℝ) ^ n) ^ p⁻¹) := fun n =>
    lt_min (lt_min hδ hr₀) (by positivity)
  have hev : ∀ n : ℕ, ∀ᶠ k in atTop, εs k < min (min δ r₀) (((1 / 2 : ℝ) ^ n) ^ p⁻¹) := fun n =>
    hεs0.eventually (Iio_mem_nhds (hc n))
  obtain ⟨φ, hφ, hφε⟩ := Filter.extraction_forall_of_eventually hev
  refine ⟨φ, hφ, fun n => (hφε n).trans_le ((min_le_left _ _).trans (min_le_left _ _)), ?_⟩
  have hbound : ∀ n, P (E (εs (φ n)))ᶜ ≤ ENNReal.ofReal |C| * ENNReal.ofReal (1 / 2) ^ n := by
    intro n
    have h1 : εs (φ n) < r₀ := (hφε n).trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have h2 : εs (φ n) ^ p ≤ (1 / 2 : ℝ) ^ n :=
      calc εs (φ n) ^ p ≤ (((1 / 2 : ℝ) ^ n) ^ p⁻¹) ^ p :=
            Real.rpow_le_rpow (hεs _).le ((hφε n).trans_le (min_le_right _ _)).le hp.le
        _ = (1 / 2 : ℝ) ^ n := Real.rpow_inv_rpow (by positivity) hp.ne'
    calc P (E (εs (φ n)))ᶜ ≤ ENNReal.ofReal (C * εs (φ n) ^ p) := hPE _ (hεs _) h1
      _ ≤ ENNReal.ofReal (|C| * (1 / 2 : ℝ) ^ n) := by
          refine ENNReal.ofReal_le_ofReal ?_
          exact (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (hεs _).le _)).trans
            (mul_le_mul_of_nonneg_left h2 (abs_nonneg C))
      _ = ENNReal.ofReal |C| * ENNReal.ofReal (1 / 2) ^ n := by
          rw [ENNReal.ofReal_mul (abs_nonneg C), ENNReal.ofReal_pow (by norm_num)]
  have hr1 : ENNReal.ofReal (1 / 2) < 1 := ENNReal.ofReal_lt_one.2 (by norm_num)
  have hsum : ∑' n, P (E (εs (φ n)))ᶜ ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.2 (tsub_pos_of_lt hr1).ne')
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  exact hω.mono fun n hn => by simpa using hn

end Equibounded

open Equibounded in
/-- **Lemma 4.7** (lemma:equibounded, line 1740) from Lemma 4.3 (`DiscreteBasicPropertiesStmt`), Lemma 2.17
(`BoundedExitTimeRVStmt`), Lemma 2.18 (`ExitTimeUpperBoundStmt`) and eq:meps-scaling (BG20 (1.8), the literature
input `MepsScalingInput`, MatedCRT/External/SLE.lean). -/
theorem equibounded_of_steps {𝒮 : SpaceFillingSLEModel} (h43 : DiscreteBasicPropertiesStmt 𝒮)
    (h17 : BoundedExitTimeRVStmt) (h18 : ExitTimeUpperBoundStmt 𝒮) (hm : MepsScalingInput 𝒮) :
    EquiboundedStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS εs hεs hεs0
  obtain ⟨α, hα, h18α⟩ := h18 γ hγ hγ2
  obtain ⟨C, hC, h18C⟩ := h18α ρ hρ hρ1
  obtain ⟨Cm, hCm, hmS⟩ := hm γ hγ hγ2
  obtain ⟨ε₀, hε₀, hmε⟩ := hmS Ω S hS
  obtain ⟨_, _, h17ρ⟩ := h17 γ hγ hγ2
  have hM := (h17ρ ((1 + ρ) / 2) (by linarith) (by linarith) Ω S.P S.hC S.hcirc S.μ hS.isConeField).1
  have hδ : 0 < min ε₀ (((1 + ρ) / 2 - ρ) ^ α⁻¹) :=
    lt_min hε₀ (Real.rpow_pos_of_pos (by linarith) _)
  obtain ⟨φ, hφ, hφδ, hBC⟩ := exists_strictMono_ae_eventually_mem (h18C Ω S hS) hεs hεs0 hδ
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hBC, h43 γ hγ hγ2 ρ hρ hρ1 Ω S hS, hM, hS.isAreaParametrized, hS.ae_tendsto_cocompact]
    with ω hBCω h43ω hMω hηω hpω
  obtain ⟨N, hN⟩ := eventually_atTop.1 hBCω
  -- the terms after the Borel-Cantelli index: Lemmas 2.17, 2.18, 4.3 and eq:meps-scaling
  have hlarge : ∀ n, N ≤ n → ∀ t, 0 < t → ∀ x,
      |rescaledMatedLeastSupersolution S ρ t (εs (φ n)) ω x| ≤
        Cm * C * (⨆ (D : Set ℂ) (_ : D ⊆ ball 0 ((1 + ρ) / 2)), largestExitTimeRV (S.μ ω) D).toReal := by
    intro n hn t ht x
    have hε := hεs (φ n)
    have hεδ := hφδ n
    obtain ⟨-, hE⟩ := hN n hn
    have hεα : εs (φ n) ^ α < (1 + ρ) / 2 - ρ :=
      calc εs (φ n) ^ α < (((1 + ρ) / 2 - ρ) ^ α⁻¹) ^ α :=
            Real.rpow_lt_rpow hε.le (hεδ.trans_le (min_le_right _ _)) hα
        _ = (1 + ρ) / 2 - ρ := Real.rpow_inv_rpow (by linarith) hα.ne'
    exact abs_rescaled_le_of_exitTime_bound hε hC (by linarith)
      (hmε _ hε (hεδ.trans_le (min_le_left _ _))).1 hεα hMω hE (h43ω t _ ht hε).1 x
  -- each of the finitely many earlier terms is bounded: `V^ε(B_ρ) \ V^ε(∂B_ρ)` is finite
  have hsmall : ∀ n, ∃ B : ℝ, ∀ t, 0 < t → ∀ x,
      |rescaledMatedLeastSupersolution S ρ t (εs (φ n)) ω x| ≤ B := by
    intro n
    have hε := hεs (φ n)
    obtain ⟨B, hB⟩ := ((ballInterior_finite (ρ := ρ) hηω.1 hpω hε).image
      (normExitTime (S.mult (εs (φ n)) ω) (ballInterior (εs (φ n)) (S.η ω) ρ))).bddAbove
    exact ⟨|S.mε (εs (φ n))|⁻¹ * max B 0, fun t ht x => abs_rescaledMatedLeastSupersolution_le
      (abs_matedLeastSupersolution_le (le_max_right _ _)
        (fun a ha => (hB ⟨a, ha, rfl⟩).trans (le_max_left _ _)) (h43ω t _ ht hε).1) x⟩
  choose B hB using hsmall
  refine ⟨max (Cm * C * (⨆ (D : Set ℂ) (_ : D ⊆ ball 0 ((1 + ρ) / 2)), largestExitTimeRV (S.μ ω) D).toReal)
    (∑ k ∈ Finset.range N, |B k|), fun t ht n x _ => ?_⟩
  by_cases hn : N ≤ n
  · exact (hlarge n hn t ht x).trans (le_max_left _ _)
  · exact (hB n t ht x).trans ((le_abs_self _).trans ((Finset.single_le_sum (fun k _ => abs_nonneg (B k))
      (Finset.mem_range.2 (not_le.1 hn))).trans (le_max_right _ _)))

end MatedCRT
