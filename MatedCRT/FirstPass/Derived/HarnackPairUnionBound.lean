import MatedCRT.FirstPass.Derived.HarnackPairEvents
import MatedCRT.FirstPass.Derived.SegmentPathOfSafeCover

/-!
# The Harnack inequality for the Green kernel from the pair events, and Lemma 5.4

Berestycki–Gwynne (2020), Lemmas 3.9–3.11 and Lemma 5.4.  The itinerary events `PairItinGood` (3.21) at the lattice
circles `∂B_{h₀ l}(h₀ (m + n i))` of mesh `h₀ = ε^{2β}` (at most `50 ε^{-6β}` of them with centre in `B_1` and
radius `h₀ l ≤ 1`) and the disconnection event `PairL311Good` of Lemma 3.11 hold with polynomially high probability
when each fails with probability at most `C ε^{α₀}` (`6β < α₀`); together with the cell size estimate the quenched
Harnack inequality `greenKernel_le_inv_mul_of_pairEvents` gives the Harnack inequality `hHarn` on circles with
constant `(p₀ p₁)⁻¹`.  `hHarn_of_pair` replaces `hHarn_of_ring`, and
`greenKernelUpperBoundStmt_of_pair_single_cellSize` replaces the ring events of Lemma 3.10 (`hRing`) by the per-circle
bounds on the events (3.21) and (3.35) in the wrapper of Lemma 5.4.
-/

set_option autoImplicit false

noncomputable section

open Set Metric MeasureTheory Filter Topology HarmonicBalls LatticeProb
open LatticeProb.LQG.LQGMeasureNonatomicMass

namespace MatedCRT

/-- A ball contained in `B_ρ(0)` has radius at most `ρ`. -/
theorem radius_le_of_ball_subset_ball_zero {z : ℂ} {R ρ : ℝ} (hR : 0 < R)
    (h : ball z R ⊆ ball (0 : ℂ) ρ) : R ≤ ρ := by
  by_contra hlt
  push Not at hlt
  have hz : ‖z‖ < ρ := mem_ball_zero_iff.1 (h (mem_ball_self hR))
  have hρ : 0 < ρ := lt_of_le_of_lt (norm_nonneg z) hz
  have h1 : ‖z + (ρ : ℂ)‖ < ρ := by
    refine mem_ball_zero_iff.1 (h ?_)
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg hρ.le]
    exact hlt
  have h2 : ‖z - (ρ : ℂ)‖ < ρ := by
    refine mem_ball_zero_iff.1 (h ?_)
    rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, Complex.norm_real,
      Real.norm_of_nonneg hρ.le]
    exact hlt
  have h3 : ‖((2 * ρ : ℝ) : ℂ)‖ ≤ ‖z + (ρ : ℂ)‖ + ‖z - (ρ : ℂ)‖ := by
    have := norm_sub_le (z + (ρ : ℂ)) (z - (ρ : ℂ))
    rwa [show (z + (ρ : ℂ)) - (z - (ρ : ℂ)) = ((2 * ρ : ℝ) : ℂ) by push_cast; ring] at this
  rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)] at h3
  linarith

/-- The box of indices `(m, n, l)` containing all lattice circles `∂B_{h l}(h (m + n i))` with `l ≥ 1`, centre in the
unit disc and radius at most `1/2`. -/
def latticeTripleBox (h : ℝ) : Finset (ℤ × ℤ × ℤ) :=
  Finset.Icc (-⌈1 / h⌉) ⌈1 / h⌉ ×ˢ Finset.Icc (-⌈1 / h⌉) ⌈1 / h⌉ ×ˢ Finset.Icc 1 ⌈1 / h⌉

/-- The admissible lattice circles: radius `h l ≥ s₁` and `B_{2 h l}(h (m + n i)) ⊆ B_{ρ''}(0)`. -/
def PairIdxOk (ρ'' h s₁ : ℝ) (i : ℤ × ℤ × ℤ) : Prop :=
  s₁ ≤ h * i.2.2 ∧ ball (latticePt h i.1 i.2.1) (2 * (h * i.2.2)) ⊆ ball (0 : ℂ) ρ''

/-- Every admissible lattice circle lies in the box. -/
theorem mem_latticeTripleBox {h s₁ ρ'' : ℝ} (hh : 0 < h) (hs₁ : 0 < s₁) (hρ : ρ'' ≤ 1) {m n l : ℤ}
    (hok : PairIdxOk ρ'' h s₁ (m, n, l)) : (m, n, l) ∈ latticeTripleBox h := by
  obtain ⟨hl, hball⟩ := hok
  have hl' : s₁ ≤ h * l := hl
  have hlpos : (0 : ℝ) < l := by
    by_contra hneg
    push Not at hneg
    nlinarith
  have hl1 : (1 : ℤ) ≤ l := by
    have : (0 : ℤ) < l := by exact_mod_cast hlpos
    omega
  have hR : 0 < 2 * (h * (l : ℝ)) := by positivity
  have hRρ := radius_le_of_ball_subset_ball_zero hR hball
  have hz : ‖latticePt h m n‖ < ρ'' := mem_ball_zero_iff.1 (hball (mem_ball_self hR))
  obtain ⟨hm, hn⟩ := abs_le_of_norm_latticePt_le hh (R := 1) (by linarith)
  have hce : (1 : ℝ) / h ≤ (⌈1 / h⌉ : ℝ) := Int.le_ceil _
  have hlh : (l : ℝ) ≤ 1 / h := by
    rw [le_div_iff₀ hh]
    nlinarith
  rw [abs_le] at hm hn
  simp only [latticeTripleBox, Finset.mem_product, Finset.mem_Icc]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨hl1, ?_⟩⟩
  · have : (-(⌈1 / h⌉ : ℤ) : ℝ) ≤ m := by linarith [hm.1]
    exact_mod_cast this
  · have : (m : ℝ) ≤ (⌈1 / h⌉ : ℤ) := by linarith [hm.2]
    exact_mod_cast this
  · have : (-(⌈1 / h⌉ : ℤ) : ℝ) ≤ n := by linarith [hn.1]
    exact_mod_cast this
  · have : (n : ℝ) ≤ (⌈1 / h⌉ : ℤ) := by linarith [hn.2]
    exact_mod_cast this
  · have : (l : ℝ) ≤ (⌈1 / h⌉ : ℤ) := by linarith
    exact_mod_cast this

/-- The box has at most `(2/h + 3)² (1/h + 1)` elements. -/
theorem card_latticeTripleBox_le {h : ℝ} (hh : 0 < h) :
    ((latticeTripleBox h).card : ℝ) ≤ (2 / h + 3) ^ 2 * (1 / h + 1) := by
  have hN : 0 ≤ ⌈1 / h⌉ := Int.ceil_nonneg (by positivity)
  have h2 : (⌈1 / h⌉ : ℝ) < 1 / h + 1 := Int.ceil_lt_add_one _
  have hc1 : ((Finset.Icc (-⌈1 / h⌉) ⌈1 / h⌉).card : ℝ) ≤ 2 / h + 3 := by
    have := card_Icc_cast_le (-⌈1 / h⌉) ⌈1 / h⌉ (by omega)
    push_cast at this
    have : (2 : ℝ) / h = 2 * (1 / h) := by ring
    linarith
  have hc2 : ((Finset.Icc 1 ⌈1 / h⌉).card : ℝ) ≤ 1 / h + 1 := by
    have := card_Icc_cast_le 1 ⌈1 / h⌉ (by omega)
    push_cast at this
    linarith
  unfold latticeTripleBox
  rw [Finset.card_product, Finset.card_product]
  push_cast
  have h0 : (0 : ℝ) ≤ ((Finset.Icc (-⌈1 / h⌉) ⌈1 / h⌉).card : ℝ) := Nat.cast_nonneg _
  have h0' : (0 : ℝ) ≤ ((Finset.Icc 1 ⌈1 / h⌉).card : ℝ) := Nat.cast_nonneg _
  calc ((Finset.Icc (-⌈1 / h⌉) ⌈1 / h⌉).card : ℝ) *
        (((Finset.Icc (-⌈1 / h⌉) ⌈1 / h⌉).card : ℝ) * ((Finset.Icc 1 ⌈1 / h⌉).card : ℝ))
      ≤ (2 / h + 3) * ((2 / h + 3) * (1 / h + 1)) := by gcongr
    _ = (2 / h + 3) ^ 2 * (1 / h + 1) := by ring

/-- For `h = ε^{2β}` the box has at most `50 ε^{-6β}` elements. -/
theorem card_latticeTripleBox_rpow_le {β ε : ℝ} (hβ : 0 < β) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ((latticeTripleBox (ε ^ (2 * β))).card : ℝ) ≤ 50 * ε ^ (-(6 * β)) := by
  have hh : 0 < ε ^ (2 * β) := Real.rpow_pos_of_pos hε0 _
  have hY1 : 1 ≤ ε ^ (-β) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε0 hε1.le (by linarith)
  have hY2 : (ε ^ (-β)) ^ 2 = (ε ^ (2 * β))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε0.le, ← Real.rpow_neg hε0.le]
    congr 1
    push_cast
    ring
  have hY6 : (ε ^ (-β)) ^ 6 = ε ^ (-(6 * β)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε0.le]
    congr 1
    push_cast
    ring
  have h1 : 2 / ε ^ (2 * β) + 3 ≤ 5 * (ε ^ (-β)) ^ 2 := by
    rw [hY2]
    have : 1 ≤ (ε ^ (2 * β))⁻¹ := by
      rw [← hY2]; nlinarith
    rw [div_eq_mul_inv]
    linarith
  have h2 : 1 / ε ^ (2 * β) + 1 ≤ 2 * (ε ^ (-β)) ^ 2 := by
    rw [hY2]
    have : 1 ≤ (ε ^ (2 * β))⁻¹ := by
      rw [← hY2]; nlinarith
    rw [one_div]
    linarith
  refine (card_latticeTripleBox_le hh).trans ?_
  have hp : (0 : ℝ) ≤ 2 / ε ^ (2 * β) + 3 := by positivity
  calc (2 / ε ^ (2 * β) + 3) ^ 2 * (1 / ε ^ (2 * β) + 1)
      ≤ (5 * (ε ^ (-β)) ^ 2) ^ 2 * (2 * (ε ^ (-β)) ^ 2) := by gcongr
    _ = 50 * (ε ^ (-β)) ^ 6 := by ring
    _ = 50 * ε ^ (-(6 * β)) := by rw [hY6]

/-- **Union bound over the lattice circles.**  If the itinerary event fails with probability at most `C ε^{α₀}` at
every circle `∂B_r(z)` with `r ≥ ε^{β₀}` and `B_{2r}(z) ⊆ B_{ρ''}(0)`, and `6β < α₀`, then with
polynomially high probability the itinerary events hold at all admissible lattice circles of mesh `ε^{2β}`. -/
theorem polyHighProb_pairItin {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (bm : Ω → MatedCRTHarmonic.MatedCRT.Path2) (η : Ω → ℝ → ℂ) {β β₀ α₀ ρ'' p₀ C : ℝ} (hβ : 0 < β)
    (h6 : 6 * β < α₀) (hC : 0 ≤ C)
    (hbad : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ z : ℂ, ∀ r : ℝ, ε ^ β₀ ≤ r → ball z (2 * r) ⊆ ball (0 : ℂ) ρ'' →
      P {ω | ¬ PairItinGood ε (bm ω) (η ω) p₀ z r} ≤ ENNReal.ofReal (C * ε ^ α₀)) :
    Gauss.PolyHighProb P fun ε => {ω | ∀ i ∈ latticeTripleBox (ε ^ (2 * β)),
      PairIdxOk ρ'' (ε ^ (2 * β)) (ε ^ β₀) i →
        PairItinGood ε (bm ω) (η ω) p₀ (latticePt (ε ^ (2 * β)) i.1 i.2.1) (ε ^ (2 * β) * i.2.2)} := by
  refine Gauss.polyHighProb_forall_mem_finset P (fun ε => latticeTripleBox (ε ^ (2 * β)))
    (fun ε i => {ω | PairIdxOk ρ'' (ε ^ (2 * β)) (ε ^ β₀) i →
      PairItinGood ε (bm ω) (η ω) p₀ (latticePt (ε ^ (2 * β)) i.1 i.2.1) (ε ^ (2 * β) * i.2.2)})
    (K := 50) (c := 6 * β) (C := C) (α := α₀) (by norm_num) hC h6
    (fun r hr hr1 => card_latticeTripleBox_rpow_le hβ hr hr1) (fun r hr hr1 i _ => ?_)
  by_cases hok : PairIdxOk ρ'' (r ^ (2 * β)) (r ^ β₀) i
  · refine (measure_mono ?_).trans (hbad r hr hr1 _ _ hok.1 hok.2)
    intro ω hω hgood
    exact hω fun _ => hgood
  · have hempty : ({ω | PairIdxOk ρ'' (r ^ (2 * β)) (r ^ β₀) i →
        PairItinGood r (bm ω) (η ω) p₀ (latticePt (r ^ (2 * β)) i.1 i.2.1) (r ^ (2 * β) * i.2.2)})ᶜ = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun ω hω => hω ?_
      show PairIdxOk _ _ _ i → _
      exact fun h => absurd h hok
    rw [hempty, measure_empty]
    exact zero_le

/-- **Harnack inequality for the Green kernel on circles** (Berestycki–Gwynne 2020, Proposition 3.8) from the cell size
estimate and the events (3.21) and (3.35) of Lemmas 3.10 and 3.11, in the form of per-circle failure bounds
(`hPair`). -/
theorem hHarn_of_pair {𝒮 : SpaceFillingSLEModel} (hsize : CellSizeEstimateStmt 𝒮)
    (hPair : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ β₀ α₀ : ℝ, 0 < β₀ ∧ 0 < α₀ ∧ ∀ ρ' : ℝ, 0 < ρ' → ρ' < 1 →
      ∃ p₀ p₁ : ℝ, 0 < p₀ ∧ 0 < p₁ ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
        (∀ z : ℂ, ∀ r : ℝ, ε ^ β₀ ≤ r → ball z (2 * r) ⊆ ball (0 : ℂ) ρ' →
          S.P {ω | ¬ PairItinGood ε (S.bm ω) (S.η ω) p₀ z r} ≤ ENNReal.ofReal (C * ε ^ α₀)) ∧
        S.P {ω | ¬ PairL311Good ε (S.bm ω) (S.η ω) ρ' (ε ^ β₀) p₁} ≤ ENNReal.ofReal (C * ε ^ α₀)) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ β : ℝ, 0 < β ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      PolyHighProb S.P fun ε => {ω | ∀ b ∈ cellVertices ε (S.η ω) (ball 0 ρ), ∀ s : ℝ,
        ε ^ β ≤ s → s ≤ (1 - ρ) / 8 →
        ∀ a ∈ cellVertices ε (S.η ω) (frontier (ball (vertexPoint ε (S.η ω) b) s)),
        ∀ y ∈ cellVertices ε (S.η ω) (frontier (ball (vertexPoint ε (S.η ω) b) s)),
          greenKernel (S.mult ε ω)
              (interiorCellVertices ε (S.η ω) (ball 0 ((1 + ρ) / 2))) a b ≤
            C₁ * greenKernel (S.mult ε ω)
              (interiorCellVertices ε (S.η ω) (ball 0 ((1 + ρ) / 2))) y b} := by
  intro γ hγ hγ2
  obtain ⟨β₀, α₀, hβ₀, hα₀, hpair⟩ := hPair γ hγ hγ2
  set e : ℝ := 1 / (2 + γ) ^ 2 with he
  have he0 : 0 < e := by positivity
  have he1 : e < 1 := by
    rw [he, div_lt_one (by positivity)]
    nlinarith
  have h2e : 2 / (2 + γ) ^ 2 - e = e := by
    rw [he]
    ring
  set β : ℝ := min (β₀ / 2) (min (e / 2) (α₀ / 14)) with hβdef
  have hβ0 : 0 < β := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hββ₀ : 2 * β ≤ β₀ := by
    have : β ≤ β₀ / 2 := min_le_left _ _
    linarith
  have hβe : β ≤ e / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hβα : β ≤ α₀ / 14 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨β, hβ0, fun ρ hρ hρ1 => ?_⟩
  obtain ⟨p₀, p₁, hp₀, hp₁, hpairp⟩ := hpair ((1 + ρ) / 2) (by linarith) (by linarith)
  refine ⟨(p₀ * p₁)⁻¹, inv_pos.2 (mul_pos hp₀ hp₁), fun Ω _ S hS => ?_⟩
  obtain ⟨C, hC⟩ := hpairp Ω S hS
  have hU : Gauss.PolyHighProb S.P _ := polyHighProb_pairItin (P := S.P) S.bm S.η (ρ'' := (1 + ρ) / 2)
    (p₀ := p₀) (C := max C 0) hβ0 (by linarith) (le_max_right _ _)
    (fun ε hε hε1 z r hr hball => ((hC ε hε hε1).1 z r hr hball).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hε.le _))))
  have hV : Gauss.PolyHighProb S.P fun ε => {ω | PairL311Good ε (S.bm ω) (S.η ω) ((1 + ρ) / 2) (ε ^ β₀) p₁} :=
    ⟨α₀, hα₀, C, 1, one_pos, fun r hr hr1 => (hC r hr hr1).2⟩
  have hsz : Gauss.PolyHighProb S.P _ :=
    hsize γ hγ hγ2 e ((1 + ρ) / 2) he0 he1 (by linarith) (by linarith) Ω S hS
  have hW : ∀ᵐ ω ∂S.P, ω ∈ {ω | HarnackQual S ω} := hS.ae_harnack_inputs hγ hγ2
  have h2 := polyHighProb_inter_ae (polyHighProb_inter (polyHighProb_inter hU hV) hsz) hW
  obtain ⟨r₁, hr₁, hr₁t⟩ := exists_rpow_le_of_small hβ0 (show (0 : ℝ) < 1 / 300 by norm_num)
  refine polyHighProb_mono_of_eventually h2 ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min r₁ 1 from lt_min hr₁ one_pos)] with ε hε
  rintro ω ⟨⟨⟨hUω, hVω⟩, hSzω⟩, hWω⟩
  obtain ⟨hηc, hall⟩ := hWω
  have hε0 : 0 < ε := hε.1
  have hε1 : ε < 1 := lt_of_lt_of_le hε.2 (min_le_right _ _)
  have hεr : ε < r₁ := lt_of_lt_of_le hε.2 (min_le_left _ _)
  obtain ⟨hlf, hcons, -, hfin⟩ := hall ε hε0
  have ht : ε ^ β ≤ 1 / 300 := hr₁t ε hε0 hεr
  have ht0 : 0 < ε ^ β := Real.rpow_pos_of_pos hε0 _
  have ht2 : ε ^ (2 * β) = (ε ^ β) ^ 2 := by
    rw [show 2 * β = β * 2 by ring, Real.rpow_mul hε0.le, Real.rpow_two]
  have hδ : ε ^ e ≤ (ε ^ β) ^ 2 := by
    rw [← ht2]
    exact Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le (by linarith)
  have hβ₀le : ε ^ β₀ ≤ (ε ^ β) ^ 2 := by
    rw [← ht2]
    exact Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le hββ₀
  have hh0 : 0 < ε ^ (2 * β) := Real.rpow_pos_of_pos hε0 _
  intro b hb s hs0 hs1 a ha y hy
  refine greenKernel_le_inv_mul_of_pairEvents (ρ := ρ) (δ := ε ^ e) (h₀ := ε ^ (2 * β)) (s₀ := ε ^ β)
    (s₁ := ε ^ β₀) (s₂ := ε ^ β₀) (p₀ := p₀) (p₁ := p₁) hε0.le (ω := S.bm ω) (η := S.η ω) hlf hcons hh0
    (Real.rpow_pos_of_pos hε0 _).le ?_ ?_ ?_ ?_ ?_ hp₀ hp₁ ?_ hVω (hfin _) b hb s hs0 hs1 a ha y hy
  · rw [ht2]
    exact hδ
  · intro k hk x hx x' hx'
    have hd := (hSzω k hk).2
    rw [h2e] at hd
    exact (Metric.dist_le_diam_of_mem ((isCompact_Icc.image hηc).isBounded) hx hx').trans hd
  · rw [ht2]
    nlinarith
  · rw [ht2]
    nlinarith
  · nlinarith
  · intro m' n' l hl hball
    exact hUω (m', n', l) (mem_latticeTripleBox hh0 (Real.rpow_pos_of_pos hε0 _) (by linarith) ⟨hl, hball⟩)
      ⟨hl, hball⟩

/-- **The Green kernel upper bound** (Berestycki–Gwynne 2020, Lemma 5.4) from the cell size estimate, the per-circle
failure bounds `hPair` of the itinerary events (3.21) and of the disconnection event (3.35) of Lemma 3.11 (which
replace the ring events of Lemma 3.10), and the single-ball estimate of Gwynne–Miller–Sheffield (2019),
Proposition 2.9 (`hsingle`). The segment path input is `segmentPathInput_holds`. -/
theorem greenKernelUpperBoundStmt_of_pair_single_cellSize {𝒮 : SpaceFillingSLEModel}
    (hsize : CellSizeEstimateStmt 𝒮)
    (hPair : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ β₀ α₀ : ℝ, 0 < β₀ ∧ 0 < α₀ ∧ ∀ ρ' : ℝ, 0 < ρ' → ρ' < 1 →
      ∃ p₀ p₁ : ℝ, 0 < p₀ ∧ 0 < p₁ ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
        (∀ z : ℂ, ∀ r : ℝ, ε ^ β₀ ≤ r → ball z (2 * r) ⊆ ball (0 : ℂ) ρ' →
          S.P {ω | ¬ PairItinGood ε (S.bm ω) (S.η ω) p₀ z r} ≤ ENNReal.ofReal (C * ε ^ α₀)) ∧
        S.P {ω | ¬ PairL311Good ε (S.bm ω) (S.η ω) ρ' (ε ^ β₀) p₁} ≤ ENNReal.ofReal (C * ε ^ α₀))
    (hsingle : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ β₀ α₀ : ℝ, 0 < β₀ ∧ 0 < α₀ ∧ ∀ ρ' : ℝ, 0 < ρ' → ρ' < 1 →
      ∃ A : ℝ, 0 < A ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ (z : ℂ) (r : ℝ), ε ^ β₀ ≤ r → ball z r ⊆ ball 0 ρ' →
          S.P {ω | ¬ ∀ T : Finset ℤ, (∀ k ∈ T, k ∈ cellVertices ε (S.η ω) (ball z r)) →
            ∑ k ∈ T, (mdeg (S.mult ε ω) k : ℝ) * diam (cell ε (S.η ω) k) ^ 2 ≤ A * r ^ 2} ≤
              ENNReal.ofReal (C * ε ^ α₀)) :
    GreenKernelUpperBoundStmt 𝒮 :=
  greenKernelUpperBoundStmt_of_inputs hsize (hHarn_of_pair hsize hPair)
    (hsum_of_ball hsize (hball_of_pointwise hsingle)) (segmentPathInput_holds 𝒮)

end MatedCRT

#print axioms MatedCRT.polyHighProb_pairItin
#print axioms MatedCRT.hHarn_of_pair
#print axioms MatedCRT.card_latticeTripleBox_rpow_le
#print axioms MatedCRT.greenKernelUpperBoundStmt_of_pair_single_cellSize
