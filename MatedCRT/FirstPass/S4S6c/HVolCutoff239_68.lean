import MatedCRT.FirstPass.S4S6c.HVolCutoff68
import MatedCRT.FirstPass.S4S6c.ShellWindowRf68

/-!
# FIRST PASS S4S6c, HVolCutoff239_68: measurable random volume cutoff and walk-a.e. volume inputs
 (l.361-542)

* `volume_lower_cutoff_measurable`, `volume_bounds_measurable_ae` (item 1): a MEASURABLE, almost surely positive cutoff
  `tVol : Ω → ℝ` such that the lower volume bounds of Lemma 2.7 (`VolumeGrowthStmt`) hold for every scale `δ < tVol ω`.
  The dyadic bad events are replaced by measurable hulls `toMeasurable` of equal measure, so no measurability of the
  field events is assumed (Borel–Cantelli for outer measures, `ae_eventually_notMem`).
* `four_mul_lt_of_radius_cap`, `measurable_radius_cap` (item 1): the radius cap `4R < t` for a walk
  radius `R ≤ d^a`, `d < 2r²`, `a = (1+ζ)/2`, when `r ≤ (t/(8·2^a))^{1/(1+ζ)}`; the cap is measurable in the field.
* `hVolC_hVolY_ae_of_cutoff` (item 2): the walk-a.e. consumer inputs `hVolC`, `hVolY` derived inside the almost-everywhere
  set by `volume_bounds_of_cutoff`, from the cutoff, the radius cap `4 R < t` and the centre bound `‖c‖ < 1 - R/4`.
* `mass_pos_of_cutoff` (item 4): local positivity `0 < μ (ball z δ)` from the cutoff, used in place of a global `hfull`.
-/
namespace MatedCRT
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
open _root_.HarmonicBalls (annulus)
namespace Lemma68Cutoff239

/-- **Measurable eventual dyadic scale (Borel–Cantelli with measurable hulls).** Let `E` satisfy the polynomially high
probability bound `PolyHighProb P E` (the dyadic events `E (2^{-m})`). There is a measurable `τ : Ω → ℝ` such that,
almost surely, `τ ω > 0` and the event `E (2^{-m})` holds at every dyadic scale `2^{-m} < τ ω`.
The bad sets are replaced by measurable supersets `toMeasurable` of the same measure, so no measurability of `E` is used.
The construction: `F j` is the set of `ω` avoiding all hulls from index `j` on (measurable), `τ` is the supremum over `j`
of `2^{-(j+N₀)} 1_{F j}`, which is measurable as a countable supremum of measurable functions. -/
theorem exists_measurable_dyadic_cutoff {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {E : ℝ → Set Ω}
    (hE : HarmonicBalls.PolyHighProb P E) :
    ∃ τ : Ω → ℝ, Measurable τ ∧ ∀ᵐ ω ∂P, 0 < τ ω ∧
      ∀ m : ℕ, (1 / 2 : ℝ) ^ m < τ ω → ω ∈ E ((1 / 2 : ℝ) ^ m) := by
  obtain ⟨p, hp, C, r₀, hr₀, hb⟩ := hE
  obtain ⟨N₀, hN₀⟩ := exists_pow_lt_of_lt_one hr₀ (by norm_num : (1 / 2 : ℝ) < 1)
  have hq0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ p := by positivity
  have hq1 : (1 / 2 : ℝ) ^ p < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hp
  have hterm : ∀ n : ℕ, P (E ((1 / 2 : ℝ) ^ (n + N₀)))ᶜ ≤ ENNReal.ofReal (|C| * ((1 / 2 : ℝ) ^ p) ^ n) := by
    intro n
    have hr : (0 : ℝ) < (1 / 2 : ℝ) ^ (n + N₀) := by positivity
    have hrr : (1 / 2 : ℝ) ^ (n + N₀) < r₀ :=
      lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_left N₀ n)) hN₀
    have hm : (1 / 2 : ℝ) ^ (n + N₀) ≤ (1 / 2 : ℝ) ^ n :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_right n N₀)
    have hpow : ((1 / 2 : ℝ) ^ n) ^ p = ((1 / 2 : ℝ) ^ p) ^ n := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2), mul_comm,
        Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2), Real.rpow_natCast]
    have hrq : ((1 / 2 : ℝ) ^ (n + N₀)) ^ p ≤ ((1 / 2 : ℝ) ^ p) ^ n := by
      rw [← hpow]; exact Real.rpow_le_rpow (by positivity) hm hp.le
    refine (hb _ hr hrr).trans (ENNReal.ofReal_le_ofReal ?_)
    exact le_trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
      (mul_le_mul_of_nonneg_left hrq (abs_nonneg C))
  have hsumm : Summable (fun n : ℕ => |C| * ((1 / 2 : ℝ) ^ p) ^ n) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  have hsum : (∑' n : ℕ, P (E ((1 / 2 : ℝ) ^ (n + N₀)))ᶜ) ≠ ∞ := by
    have hle : (∑' n : ℕ, P (E ((1 / 2 : ℝ) ^ (n + N₀)))ᶜ)
        ≤ ENNReal.ofReal (∑' n : ℕ, |C| * ((1 / 2 : ℝ) ^ p) ^ n) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsumm]
      exact ENNReal.tsum_le_tsum hterm
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  -- measurable hulls `G n` of the bad sets, with the same measure
  obtain ⟨G, hG⟩ : ∃ G : ℕ → Set Ω, ∀ n : ℕ, G n = toMeasurable P (E ((1 / 2 : ℝ) ^ (n + N₀)))ᶜ :=
    ⟨fun n => toMeasurable P (E ((1 / 2 : ℝ) ^ (n + N₀)))ᶜ, fun n => rfl⟩
  have hGm : ∀ n, MeasurableSet (G n) := fun n => by rw [hG]; exact measurableSet_toMeasurable _ _
  have hGP : ∀ n, P (G n) = P (E ((1 / 2 : ℝ) ^ (n + N₀)))ᶜ := fun n => by
    rw [hG]; exact measure_toMeasurable _
  have hsub : ∀ n, (E ((1 / 2 : ℝ) ^ (n + N₀)))ᶜ ⊆ G n := fun n => by
    rw [hG]; exact subset_toMeasurable _ _
  have hGsum : ∑' n : ℕ, P (G n) ≠ ∞ := by simpa only [hGP] using hsum
  have hBC : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∉ G n := ae_eventually_notMem hGsum
  -- `F j`: the points avoiding every hull from index `j` on (a measurable set)
  obtain ⟨F, hF⟩ : ∃ F : ℕ → Set Ω, ∀ j ω, ω ∈ F j ↔ ∀ n : ℕ, j ≤ n → ω ∉ G n :=
    ⟨fun j => {ω | ∀ n : ℕ, j ≤ n → ω ∉ G n}, fun j ω => Iff.rfl⟩
  have hFm : ∀ j, MeasurableSet (F j) := by
    intro j
    have hset : F j = ⋂ n : ℕ, ⋂ (_ : j ≤ n), (G n)ᶜ := by
      ext ω
      simp only [mem_iInter, mem_compl_iff, hF]
    rw [hset]
    exact MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ => (hGm n).compl
  -- the cutoff: the supremum over `j` of the scales `2^{-(j+N₀)}` on `F j`
  obtain ⟨τ, hτdef⟩ : ∃ τ : Ω → ℝ, ∀ ω, τ ω = ⨆ j : ℕ, (F j).indicator (fun _ => (1 / 2 : ℝ) ^ (j + N₀)) ω :=
    ⟨fun ω => ⨆ j : ℕ, (F j).indicator (fun _ => (1 / 2 : ℝ) ^ (j + N₀)) ω, fun ω => rfl⟩
  have hτm : Measurable τ := by
    have hfun : τ = fun ω => ⨆ j : ℕ, (F j).indicator (fun _ => (1 / 2 : ℝ) ^ (j + N₀)) ω :=
      funext hτdef
    rw [hfun]
    exact Measurable.iSup fun j => measurable_const.indicator (hFm j)
  have hind_le : ∀ j ω, (F j).indicator (fun _ => (1 / 2 : ℝ) ^ (j + N₀)) ω ≤ 1 := by
    intro j ω
    by_cases h : ω ∈ F j
    · rw [indicator_of_mem h]; exact pow_le_one₀ (by norm_num) (by norm_num)
    · rw [indicator_of_notMem h]; norm_num
  have hbdd : ∀ ω, BddAbove (Set.range fun j : ℕ => (F j).indicator (fun _ => (1 / 2 : ℝ) ^ (j + N₀)) ω) :=
    fun ω => ⟨1, by rintro _ ⟨j, rfl⟩; exact hind_le j ω⟩
  refine ⟨τ, hτm, ?_⟩
  filter_upwards [hBC] with ω hω
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp hω
  have hωF₀ : ω ∈ F j₀ := (hF j₀ ω).mpr fun n hn => hj₀ n hn
  have hpos : 0 < τ ω := by
    rw [hτdef ω]
    refine lt_of_lt_of_le ?_ (le_ciSup (hbdd ω) j₀)
    rw [indicator_of_mem hωF₀]
    positivity
  refine ⟨hpos, fun m hm => ?_⟩
  rw [hτdef ω] at hm
  obtain ⟨j, hj⟩ := exists_lt_of_lt_ciSup hm
  by_cases hωj : ω ∈ F j
  · rw [indicator_of_mem hωj] at hj
    have hlt : j + N₀ < m := by
      by_contra hcon
      have hle : m ≤ j + N₀ := not_lt.mp hcon
      have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) hle
      linarith
    have hnot : ω ∉ G (m - N₀) := (hF j ω).mp hωj (m - N₀) (by omega)
    have hm' : m - N₀ + N₀ = m := by omega
    by_contra hE'
    apply hnot
    apply hsub (m - N₀)
    rw [hm']
    exact hE'
  · rw [indicator_of_notMem hωj] at hj
    exact absurd hj (not_lt.mpr (by positivity))

/-- **Measurable random volume cutoff, almost surely (Lemma 2.7 at dyadic scales, measurable).** For the quantum cone
field `μ` (`IsConeField`) and `γ ∈ (0,2)`, every `β > (2+γ)²/2` has a MEASURABLE cutoff `tVol : Ω → ℝ`, almost surely
positive, with `μ ω (B_δ(z)) ≥ δ^β` for all `0 < δ < tVol ω` and all `z ∈ B_{1-δ}`. The cutoff is never claimed for
every `ω`. The proof is `volume_lower_cutoff_ae` with the random index replaced by `exists_measurable_dyadic_cutoff`. -/
theorem volume_lower_cutoff_measurable {γ β : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hβ : (2 + γ) ^ 2 / 2 < β)
    (hVG : VolumeGrowthStmt) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (hcone : IsConeField γ P hC hcirc μ) :
    ∃ tVol : Ω → ℝ, Measurable tVol ∧ ∀ᵐ ω ∂P, 0 < tVol ω ∧
      ∀ δ : ℝ, 0 < δ → δ < tVol ω → ∀ z ∈ ball (0 : ℂ) (1 - δ), ENNReal.ofReal (δ ^ β) ≤ μ ω (ball z δ) := by
  set β₀ : ℝ := ((2 + γ) ^ 2 / 2 + β) / 2 with hβ₀def
  have hβ₀ : (2 + γ) ^ 2 / 2 < β₀ := by rw [hβ₀def]; linarith
  have hβ₀β : β₀ < β := by rw [hβ₀def]; linarith
  have hβ₀pos : 0 < β₀ := lt_trans (by positivity) hβ₀
  have h2γ : 0 < 2 - γ := by linarith
  have hβp : 0 < (2 - γ) ^ 2 / 4 := by positivity
  have hβpl : (2 - γ) ^ 2 / 4 < (2 - γ) ^ 2 / 2 := by
    have : 0 < (2 - γ) ^ 2 := by positivity
    linarith
  have hE := hVG γ hγ0 hγ2 ((2 - γ) ^ 2 / 4) β₀ hβp hβpl hβ₀ Ω P hC hcirc μ hcone
  obtain ⟨τ, hτm, hτ⟩ := exists_measurable_dyadic_cutoff hE
  refine ⟨fun ω => min (τ ω) ((1 / 2 : ℝ) ^ (β₀ / (β - β₀))), hτm.min measurable_const, ?_⟩
  filter_upwards [hτ] with ω hω
  obtain ⟨hτpos, hτω⟩ := hω
  refine ⟨lt_min hτpos (by positivity), ?_⟩
  intro δ hδ0 hδt z hz
  have hδτ : δ < τ ω := lt_of_lt_of_le hδt (min_le_left _ _)
  have hδe : δ < (1 / 2 : ℝ) ^ (β₀ / (β - β₀)) := lt_of_lt_of_le hδt (min_le_right _ _)
  have hδ1 : δ < 1 := lt_of_lt_of_le hδe (Real.rpow_le_one (by norm_num) (by norm_num) (by positivity))
  -- `δ^(β - β₀) ≤ (1/2)^β₀`
  have hpow : δ ^ (β - β₀) ≤ (1 / 2 : ℝ) ^ β₀ := by
    calc δ ^ (β - β₀) ≤ ((1 / 2 : ℝ) ^ (β₀ / (β - β₀))) ^ (β - β₀) :=
          Real.rpow_le_rpow hδ0.le hδe.le (by linarith)
      _ = (1 / 2 : ℝ) ^ β₀ := by
          rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
          congr 1
          exact div_mul_cancel₀ β₀ (sub_pos.mpr hβ₀β).ne'
  -- the dyadic scale `q = 2^{-(n+1)} ∈ [δ/2, δ)`
  have h1 : (1 : ℝ) ≤ 1 / δ := by rw [le_div_iff₀ hδ0]; linarith
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near h1 (by norm_num : (1 : ℝ) < 2)
  have hA : 1 < (2 : ℝ) ^ (n + 1) * δ := (div_lt_iff₀ hδ0).mp hn2
  have hB : (2 : ℝ) ^ n * δ ≤ 1 := (le_div_iff₀ hδ0).mp hn1
  have hqinv : (1 / 2 : ℝ) ^ (n + 1) * (2 : ℝ) ^ (n + 1) = 1 := by
    rw [← mul_pow]; norm_num
  have hqpos : (0 : ℝ) < (1 / 2 : ℝ) ^ (n + 1) := by positivity
  have h2n1 : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
  have hqδ : (1 / 2 : ℝ) ^ (n + 1) < δ := by
    by_contra hcon
    have hc : δ ≤ (1 / 2 : ℝ) ^ (n + 1) := not_lt.mp hcon
    have := mul_le_mul_of_nonneg_right hc (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (n + 1))
    rw [hqinv] at this
    linarith
  have hhalf : δ / 2 ≤ (1 / 2 : ℝ) ^ (n + 1) := by
    by_contra hcon
    have hc : (1 / 2 : ℝ) ^ (n + 1) < δ / 2 := not_le.mp hcon
    have := mul_lt_mul_of_pos_right hc (pow_pos (by norm_num : (0 : ℝ) < 2) (n + 1))
    rw [hqinv] at this
    have h3 : δ / 2 * (2 : ℝ) ^ (n + 1) = δ * 2 ^ n := by rw [h2n1]; ring
    linarith
  have hqτ : (1 / 2 : ℝ) ^ (n + 1) < τ ω := lt_trans hqδ hδτ
  set q : ℝ := (1 / 2 : ℝ) ^ (n + 1) with hqdef
  have hωq : ∀ w ∈ ball (0 : ℂ) (1 - q), ENNReal.ofReal (q ^ β₀) ≤ μ ω (ball w q) :=
    fun w hw => (hτω (n + 1) hqτ w hw).1
  have hzq : z ∈ ball (0 : ℂ) (1 - q) := by
    rw [mem_ball_zero_iff] at hz ⊢
    linarith
  have hlow : ENNReal.ofReal (q ^ β₀) ≤ μ ω (ball z q) := hωq z hzq
  have hmono : μ ω (ball z q) ≤ μ ω (ball z δ) := measure_mono (ball_subset_ball hqδ.le)
  have hdelta : δ ^ β ≤ q ^ β₀ := by
    have hsplit : δ ^ β = δ ^ β₀ * δ ^ (β - β₀) := by
      rw [← Real.rpow_add hδ0]; congr 1; ring
    have hhalfpow : (δ / 2) ^ β₀ = δ ^ β₀ * (1 / 2 : ℝ) ^ β₀ := by
      rw [show δ / 2 = δ * (1 / 2) by ring, Real.mul_rpow hδ0.le (by norm_num)]
    calc δ ^ β = δ ^ β₀ * δ ^ (β - β₀) := hsplit
      _ ≤ δ ^ β₀ * (1 / 2 : ℝ) ^ β₀ := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = (δ / 2) ^ β₀ := hhalfpow.symm
      _ ≤ q ^ β₀ := Real.rpow_le_rpow (by positivity) hhalf hβ₀pos.le
  exact (ENNReal.ofReal_le_ofReal hdelta).trans (hlow.trans hmono)

/-- **Almost-sure form of the measurable random-radius volume bounds.** Same cutoff as
`volume_lower_cutoff_measurable`; for almost every `ω`, every radius `0 < R` with `R/4 < tVol ω` and every centre
`‖z‖ < 1 - R/4` satisfy the two consumer bounds of `volume_bounds_of_cutoff` for the field `μ ω`. -/
theorem volume_bounds_measurable_ae {γ β c0 : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hβ : (2 + γ) ^ 2 / 2 < β)
    (hc0 : 0 < c0) (hc0' : c0 ≤ 1 / 4)
    (hVG : VolumeGrowthStmt) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (hcone : IsConeField γ P hC hcirc μ) :
    ∃ tVol : Ω → ℝ, Measurable tVol ∧ ∀ᵐ ω ∂P, 0 < tVol ω ∧
      ∀ R : ℝ, 0 < R → R / 4 < tVol ω → ∀ z : ℂ, ‖z‖ < 1 - R / 4 →
        ENNReal.ofReal ((c0 * R) ^ β) ≤ μ ω (ball z (c0 * R)) ∧
          ∀ y ∈ ball (0 : ℂ) (1 - R / 4), ENNReal.ofReal ((R / 4) ^ β) ≤ μ ω (ball y (R / 4)) := by
  obtain ⟨tVol, htm, hae⟩ := volume_lower_cutoff_measurable hγ0 hγ2 hβ hVG Ω P hC hcirc μ hcone
  refine ⟨tVol, htm, hae.mono fun ω hω => ⟨hω.1, fun R hR hRt z hz => ?_⟩⟩
  exact Lemma68Cutoff.volume_bounds_of_cutoff hc0 hc0' hR hω.2 hRt hz

/-- **Radius cap (deterministic).** Let `a = (1+ζ)/2`, `ζ > 0`, `0 < d < 2r²` and `R ≤ d^a` (the window radius of
`windowRfT_bounds`, with `d = dyadicD r`). If `r ≤ (t/(8·2^a))^{1/(1+ζ)}` then `4R < t`. The constant `8` gives strict
slack at the non-strict endpoint. -/
theorem four_mul_lt_of_radius_cap {t ζ a d r R : ℝ} (ha : a = (1 + ζ) / 2) (hζ : 0 < ζ) (ht : 0 < t)
    (hr : 0 < r) (hd0 : 0 < d) (hd2 : d < 2 * r ^ 2) (hRd : R ≤ d ^ a)
    (hrt : r ≤ (t / (8 * 2 ^ a)) ^ (1 / (1 + ζ))) : 4 * R < t := by
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have h2a : (0 : ℝ) < 2 ^ a := by positivity
  have hdpow : d ^ a ≤ (2 * r ^ 2) ^ a := Real.rpow_le_rpow hd0.le hd2.le ha0
  have e : ((2 : ℕ) : ℝ) * a = 1 + ζ := by rw [ha]; push_cast; ring
  have hpow : (2 * r ^ 2) ^ a = 2 ^ a * r ^ (1 + ζ) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hr.le, e]
  rw [hpow] at hdpow
  have hrpow : r ^ (1 + ζ) ≤ t / (8 * 2 ^ a) := by
    calc r ^ (1 + ζ) ≤ ((t / (8 * 2 ^ a)) ^ (1 / (1 + ζ))) ^ (1 + ζ) :=
          Real.rpow_le_rpow hr.le hrt (by linarith)
      _ = t / (8 * 2 ^ a) := by
          rw [← Real.rpow_mul (by positivity), one_div_mul_cancel (by linarith : (0 : ℝ) < 1 + ζ).ne',
            Real.rpow_one]
  have hX : 2 ^ a * r ^ (1 + ζ) ≤ t / 8 := by
    calc 2 ^ a * r ^ (1 + ζ) ≤ 2 ^ a * (t / (8 * 2 ^ a)) := mul_le_mul_of_nonneg_left hrpow h2a.le
      _ = t / 8 := by field_simp
  linarith

/-- **Measurable radius cap.** The cap `min 1 ((t ω/(8·2^a))^{1/(1+ζ)})` is measurable in the field when `t` is. -/
theorem measurable_radius_cap {Ω : Type} [MeasurableSpace Ω] {tVol : Ω → ℝ} (htm : Measurable tVol) (a ζ : ℝ) :
    Measurable (fun ω => min 1 ((tVol ω / (8 * 2 ^ a)) ^ (1 / (1 + ζ)))) :=
  measurable_const.min ((htm.div_const _).pow_const _)

/-- **Walk-a.e. consumer inputs from the cutoff.** Let `ν` be the law of the walk and `pre` the prefix event. If, almost
surely on `pre`, the radius is positive, `4 R < t` and the centre satisfies `‖c‖ < 1 - R/4`, and the field satisfies the
cutoff bound below `t`, then the two consumer volume inputs `hVolC`, `hVolY` hold almost surely on `pre`. They are
derived inside the almost-everywhere set by `volume_bounds_of_cutoff`; no universal statement over all paths is used. -/
theorem hVolC_hVolY_ae_of_cutoff {Ω' : Type} [MeasurableSpace Ω'] {ν : Measure Ω'} {μ : Measure ℂ}
    {β c0 t : ℝ} (hc0 : 0 < c0) (hc0' : c0 ≤ 1 / 4) (ht : 0 < t)
    (hcut : ∀ δ : ℝ, 0 < δ → δ < t → ∀ z ∈ ball (0 : ℂ) (1 - δ), ENNReal.ofReal (δ ^ β) ≤ μ (ball z δ))
    {pre : Ω' → Prop} {R : Ω' → ℝ} {c : Ω' → ℂ}
    (hR0 : ∀ᵐ x ∂ν, pre x → 0 < R x) (hRt : ∀ᵐ x ∂ν, pre x → 4 * R x < t)
    (hc : ∀ᵐ x ∂ν, pre x → ‖c x‖ < 1 - R x / 4) :
    (∀ᵐ x ∂ν, pre x → ENNReal.ofReal ((c0 * R x) ^ β) ≤ μ (ball (c x) (c0 * R x))) ∧
      (∀ᵐ x ∂ν, pre x → ∀ y ∈ ball (0 : ℂ) (1 - R x / 4),
        ENNReal.ofReal ((R x / 4) ^ β) ≤ μ (ball y (R x / 4))) := by
  have key : ∀ᵐ x ∂ν, pre x → ENNReal.ofReal ((c0 * R x) ^ β) ≤ μ (ball (c x) (c0 * R x)) ∧
      ∀ y ∈ ball (0 : ℂ) (1 - R x / 4), ENNReal.ofReal ((R x / 4) ^ β) ≤ μ (ball y (R x / 4)) := by
    filter_upwards [hR0, hRt, hc] with x h0 h1 h2 hpre
    exact Lemma68Cutoff.volume_bounds_of_cutoff hc0 hc0' (h0 hpre) hcut (by linarith [h1 hpre]) (h2 hpre)
  exact ⟨key.mono fun x hx hpre => (hx hpre).1, key.mono fun x hx hpre => (hx hpre).2⟩

/-- **Local positivity of the ball masses (replaces a global full-support hypothesis).** Below the cutoff, the mass of
every ball `B_δ(z)` with `z ∈ B_{1-δ}` is positive, by the lower bound `δ^β > 0`. -/
theorem mass_pos_of_cutoff {μ : Measure ℂ} {β t δ : ℝ} {z : ℂ}
    (hcut : ∀ δ' : ℝ, 0 < δ' → δ' < t → ∀ z' ∈ ball (0 : ℂ) (1 - δ'),
      ENNReal.ofReal (δ' ^ β) ≤ μ (ball z' δ'))
    (hδ : 0 < δ) (hδt : δ < t) (hz : z ∈ ball (0 : ℂ) (1 - δ)) : 0 < μ (ball z δ) :=
  lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hδ β)) (hcut δ hδ hδt z hz)

/-- **Positivity of an annulus infimum from the cutoff (no full support).** If every centre `w ∈ S` lies in
`B_{1-R/4}` and `R/4 < t`, then `⨅ w ∈ S, μ (B_{c₀R}(w)) ≥ (c₀R)^β > 0` by `volume_bounds_of_cutoff`. The consumer
`pos_iInf_annulus_ball` (HoneGoodEvent68.lean:119) instead needs positivity at the cover minimiser at radius `c₀R/2`;
the containment `S ⊆ B_{1-R/4}` is not among that consumer's hypotheses. -/
theorem pos_iInf_of_cutoff {μ : Measure ℂ} {β t c0 R : ℝ} {S : Set ℂ} (hc0 : 0 < c0) (hc0' : c0 ≤ 1 / 4) (hR : 0 < R)
    (hcut : ∀ δ : ℝ, 0 < δ → δ < t → ∀ z ∈ ball (0 : ℂ) (1 - δ), ENNReal.ofReal (δ ^ β) ≤ μ (ball z δ))
    (hRt : R / 4 < t) (hS : ∀ w ∈ S, ‖w‖ < 1 - R / 4) :
    0 < ⨅ w ∈ S, μ (ball w (c0 * R)) :=
  lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (mul_pos hc0 hR) β))
    (le_iInf₂ fun w hw => (Lemma68Cutoff.volume_bounds_of_cutoff hc0 hc0' hR hcut hRt (hS w hw)).1)

/-- **The annulus of an eligible shell centre lies in the cutoff domain.** Let `z ∈ shortEligible ρ d a`,
so `‖z‖ < ρ - 3 d^a`, and let `0 < R ≤ d^a` with `ρ < 1`. For `w ∈ 𝔸_{R,2R}(z) = B_{2R}(z) \ closedBall z R`:
`‖w‖ ≤ ‖z‖ + dist w z < ρ - 3 d^a + 2R ≤ ρ - R < 1 - R/4`. -/
theorem norm_lt_of_mem_annulus_eligible {ρ d a R : ℝ} {z w : ℂ} (hρ : ρ < 1) (hz : z ∈ Lemma68Window.shortEligible ρ d a)
    (hR0 : 0 < R) (hRs : R ≤ d ^ a) (hw : w ∈ annulus z R (2 * R)) : ‖w‖ < 1 - R / 4 := by
  have hzn : ‖z‖ < ρ - 3 * d ^ a := by
    have hzb : z ∈ ball (0 : ℂ) (ρ - 3 * d ^ a) := hz.1.1
    rwa [mem_ball_zero_iff] at hzb
  have hwz : dist w z < 2 * R := mem_ball.mp hw.1
  have htri : ‖w‖ - ‖z‖ ≤ ‖w - z‖ := norm_sub_norm_le w z
  rw [← dist_eq_norm] at htri
  linarith

/-- **Positivity of the annulus infimum at an eligible centre.** The corrected local form of
`pos_iInf_annulus_ball`: no full support is used; the cutoff bound below `t` and `4R < t` (`R/4 < t`) suffice, because
the whole annulus `𝔸_{R,2R}(z)` lies in `B_{1-R/4}` by `norm_lt_of_mem_annulus_eligible`. -/
theorem pos_iInf_annulus_of_eligible {μ : Measure ℂ} {β t c0 ρ d a R : ℝ} {z : ℂ} (hc0 : 0 < c0) (hc0' : c0 ≤ 1 / 4)
    (hρ : ρ < 1) (hz : z ∈ Lemma68Window.shortEligible ρ d a) (hR0 : 0 < R) (hRs : R ≤ d ^ a) (hRt : R / 4 < t)
    (hcut : ∀ δ : ℝ, 0 < δ → δ < t → ∀ z' ∈ ball (0 : ℂ) (1 - δ), ENNReal.ofReal (δ ^ β) ≤ μ (ball z' δ)) :
    0 < ⨅ w ∈ annulus z R (2 * R), μ (ball w (c0 * R)) :=
  pos_iInf_of_cutoff hc0 hc0' hR0 hcut hRt (fun _ hw => norm_lt_of_mem_annulus_eligible hρ hz hR0 hRs hw)

/-- **Almost-sure corrected `hpos`, walk form.** For a walk law `ν`, a prefix event `pre`, shell
centres `z x` and walk radii `R x`: if almost surely on `pre`, the centre is eligible (`z x ∈ shortEligible ρ d a`), the
radius is positive, `R x ≤ d^a` and `4 R x < t`, and the cutoff bound holds below `t` for the field `μ`, then the annulus
infimum at `z x` with radius `R x` is almost surely positive on `pre`. No full support and no centre-only `hVolC` is used.
Consumer: `HoneGoodEventAe68.hpos_ae` must take `Z k x = shellCentre … k x` and the binders `hEl`, `hRs` (see report). -/
theorem hpos_ae_of_eligible {Ω' : Type} [MeasurableSpace Ω'] {ν : Measure Ω'} {μ : Measure ℂ}
    {ρ d a β c0 t : ℝ} (hc0 : 0 < c0) (hc0' : c0 ≤ 1 / 4) (hρ : ρ < 1)
    (hcut : ∀ δ : ℝ, 0 < δ → δ < t → ∀ z' ∈ ball (0 : ℂ) (1 - δ), ENNReal.ofReal (δ ^ β) ≤ μ (ball z' δ))
    {pre : Ω' → Prop} {R : Ω' → ℝ} {z : Ω' → ℂ}
    (hEl : ∀ᵐ x ∂ν, pre x → z x ∈ Lemma68Window.shortEligible ρ d a)
    (hR0 : ∀ᵐ x ∂ν, pre x → 0 < R x) (hRs : ∀ᵐ x ∂ν, pre x → R x ≤ d ^ a)
    (hRt : ∀ᵐ x ∂ν, pre x → 4 * R x < t) :
    ∀ᵐ x ∂ν, pre x → 0 < ⨅ w ∈ annulus (z x) (R x) (2 * R x), μ (ball w (c0 * R x)) := by
  filter_upwards [hEl, hR0, hRs, hRt] with x h1 h2 h3 h4 hpre
  exact pos_iInf_annulus_of_eligible hc0 hc0' hρ (h1 hpre) (h2 hpre) (h3 hpre) (by linarith [h4 hpre, h2 hpre]) hcut

end Lemma68Cutoff239
end MatedCRT

#print axioms MatedCRT.Lemma68Cutoff239.exists_measurable_dyadic_cutoff
#print axioms MatedCRT.Lemma68Cutoff239.volume_lower_cutoff_measurable
#print axioms MatedCRT.Lemma68Cutoff239.volume_bounds_measurable_ae
#print axioms MatedCRT.Lemma68Cutoff239.four_mul_lt_of_radius_cap
#print axioms MatedCRT.Lemma68Cutoff239.measurable_radius_cap
#print axioms MatedCRT.Lemma68Cutoff239.hVolC_hVolY_ae_of_cutoff
#print axioms MatedCRT.Lemma68Cutoff239.mass_pos_of_cutoff
#print axioms MatedCRT.Lemma68Cutoff239.pos_iInf_of_cutoff
#print axioms MatedCRT.Lemma68Cutoff239.norm_lt_of_mem_annulus_eligible
#print axioms MatedCRT.Lemma68Cutoff239.pos_iInf_annulus_of_eligible
#print axioms MatedCRT.Lemma68Cutoff239.hpos_ae_of_eligible
