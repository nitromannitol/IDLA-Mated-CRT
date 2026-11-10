import MatedCRT.Proofs.Sec4.ObstacleSpecialization.Escape
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells
import MatedCRT.Steps.Sec3.PolynomialGoodEventIntersection
import MatedCRT.FirstPass.S3i.LensDefs
import MatedCRT.FirstPass.S3t.CellGeometry
import MatedCRT.Proofs.Sec4.ObstacleSpecialization.Statements
import MatedCRT.FirstPass.S3i.Frozen
import MatedCRT.External.SLE
import MatedCRT.Draft.Section2

/-!
# Common polynomially good environment (plan CHATGPT-221, section 3, Lemma 3; owner q4, task H3)

Part A (this stage): the discrete and probabilistic helpers used by Lemma 3.
* `exists_chain_forward`, `exists_vPath_to_boundary`: a finite set `A` of vertices, with consecutive edges
  `m k (k+1) ≠ 0`, is exited from every `a ∈ A` by a path in `vClosure m A` (the walk-exit half of `FiniteExitData`).
* `mdeg_pos_of_edge`: the degree is positive at a vertex with an edge (`mdeg` is a finite sum, `IsLocallyFiniteMult`).
* `polyHighProb_inter`, `polyHighProb_const_of_ae`: `PolyHighProb` is stable under finite intersection, and
  an almost sure event is `PolyHighProb` (Harmonic-Balls convention, `HarmonicBalls.PolyHighProb`).
* `exponent_b_facts`, `scale_facts`: the gamma-only exponent `b_γ = 1/(2+γ)^2` of the verdict, and the radii
  `ρ₀ = (2ρ+1)/3`, `ρ₁ = (ρ+2)/3` of Lemma 3 (note `(1+ρ₀)/2 = ρ₁`, so `TruncatedLaws.vertexOf_mem_interiorCellVertices_of_mesh`
  applies with radius `ρ₀`).

Terminology: Armstrong-Kuusi-Mourrat (quenched walk `srwLaw`, exit path), Armitage-Gardiner (boundary `∂A`, closure).
-/

namespace MatedCRT
namespace FirstPass36

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

/-- A forward chain of edges: if `a, a+1, …, a+N-1` lie in `A` and `a+N ∈ vClosure m A`, then there is a list from
`a` to `a+N` whose entries lie in `vClosure m A` and whose consecutive entries are joined by edges. -/
theorem exists_chain_forward {m : ℤ → ℤ → ℕ} (hsucc : ∀ k : ℤ, m k (k + 1) ≠ 0) {A : Set ℤ} :
    ∀ (N : ℕ) (a : ℤ), (∀ i : ℕ, i < N → a + (i : ℤ) ∈ A) → a + (N : ℤ) ∈ vClosure m A →
      ∃ p : List ℤ, p.head? = some a ∧ p.getLast? = some (a + (N : ℤ)) ∧
        (∀ c ∈ p, c ∈ vClosure m A) ∧ p.IsChain (fun c d => m c d ≠ 0) := by
  intro N
  induction N with
  | zero =>
    intro a _ h0
    refine ⟨[a], rfl, by simp, ?_, List.isChain_singleton _⟩
    intro c hc
    rw [List.mem_singleton] at hc
    subst hc
    simpa using h0
  | succ N ih =>
    intro a hA hN
    have haA : a ∈ A := by simpa using hA 0 (Nat.succ_pos N)
    have e : ∀ i : ℕ, a + ((i + 1 : ℕ) : ℤ) = a + 1 + (i : ℤ) := fun i => by push_cast; ring
    obtain ⟨p, hhead, hlast, hmem, hchain⟩ := ih (a + 1)
      (fun i hi => by
        have := hA (i + 1) (by omega)
        rw [e i] at this
        exact this)
      (by
        have := hN
        rw [e N] at this
        exact this)
    cases p with
    | nil => simp at hhead
    | cons b rest =>
      have hb : b = a + 1 := by simpa using hhead
      subst hb
      refine ⟨a :: (a + 1) :: rest, rfl, ?_, ?_, ?_⟩
      · rw [List.getLast?_cons_cons]
        rw [hlast]
        congr 1
        push_cast
        ring
      · intro c hc
        rcases List.mem_cons.1 hc with rfl | hc
        · exact Or.inl haA
        · exact hmem c hc
      · rw [List.isChain_cons_cons]
        exact ⟨hsucc a, hchain⟩

/-- **Exit of a finite set by edges (the walk-exit half of `FiniteExitData`).** If `A` is finite, consecutive edges
`m k (k+1) ≠ 0` exist, and `a ∈ A`, then some boundary vertex `b ∈ ∂A` is joined to `a` by a path inside `cl(A) = A ∪ ∂A`. -/
theorem exists_vPath_to_boundary {m : ℤ → ℤ → ℕ} (hsucc : ∀ k : ℤ, m k (k + 1) ≠ 0)
    {A : Set ℤ} (hA : A.Finite) {a : ℤ} (ha : a ∈ A) :
    ∃ b ∈ vBoundary m A, ∃ p : List ℤ, IsVPathIn m (vClosure m A) p a b := by
  classical
  have hex : ∃ n : ℕ, a + (n : ℤ) ∉ A := by
    by_contra h
    simp only [not_exists, not_not] at h
    have hinj : Function.Injective (fun n : ℕ => a + (n : ℤ)) := by
      intro i j hij
      simpa using hij
    have hsub : Set.range (fun n : ℕ => a + (n : ℤ)) ⊆ A := by
      rintro _ ⟨n, rfl⟩
      exact h n
    exact (Set.infinite_range_of_injective hinj) (hA.subset hsub)
  obtain ⟨N, hNspec, hlt⟩ : ∃ N : ℕ, a + (N : ℤ) ∉ A ∧ ∀ i : ℕ, i < N → a + (i : ℤ) ∈ A :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => by simpa using Nat.find_min hex hi⟩
  have hN0 : N ≠ 0 := by
    intro h0
    rw [h0] at hNspec
    exact hNspec (by simpa using ha)
  obtain ⟨M, hM⟩ : ∃ M : ℕ, N = M + 1 := ⟨N - 1, by omega⟩
  have hbd : a + (N : ℤ) ∈ vBoundary m A := by
    show a + (N : ℤ) ∉ A ∧ ∃ x ∈ A, m x (a + (N : ℤ)) ≠ 0
    refine ⟨hNspec, a + (M : ℤ), hlt M (by omega), ?_⟩
    have e : a + (N : ℤ) = a + (M : ℤ) + 1 := by
      rw [hM]
      push_cast
      ring
    rw [e]
    exact hsucc (a + (M : ℤ))
  obtain ⟨p, hhead, hlast, hmem, hchain⟩ :=
    exists_chain_forward hsucc N a hlt (Or.inr hbd)
  refine ⟨a + (N : ℤ), hbd, p, ?_⟩
  unfold IsVPathIn
  exact ⟨hhead, hlast, hmem, hchain⟩

/-- The degree of a vertex with an edge is positive (`mdeg` is a finite sum over the locally finite row). -/
theorem mdeg_pos_of_edge {m : ℤ → ℤ → ℕ} (hloc : IsLocallyFiniteMult m) {a b : ℤ} (h : m a b ≠ 0) :
    0 < mdeg m a := by
  unfold mdeg
  have hfin : (Function.support fun c => m a c).Finite := hloc a
  have hpos : 0 < m a b := Nat.pos_of_ne_zero h
  exact lt_of_lt_of_le hpos (single_le_finsum b hfin (fun j => Nat.zero_le _))

/-- `PolyHighProb` is stable under intersection (union bound, `measure_compl_inter_le_polynomial`). -/
theorem polyHighProb_inter {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E F : ℝ → Set Ω}
    (hE : PolyHighProb P E) (hF : PolyHighProb P F) :
    PolyHighProb P (fun r => E r ∩ F r) := by
  obtain ⟨p, hp, C, r₀, hr₀, hEb⟩ := hE
  obtain ⟨q, hq, D, s₀, hs₀, hFb⟩ := hF
  unfold PolyHighProb
  refine ⟨min p q, lt_min hp hq, max C 0 + max D 0, min r₀ (min s₀ 1), lt_min hr₀ (lt_min hs₀ one_pos), ?_⟩
  intro r hr hrlt
  have hr₀' : r < r₀ := lt_of_lt_of_le hrlt (min_le_left _ _)
  have hs₀' : r < s₀ := lt_of_lt_of_le hrlt ((min_le_right _ _).trans (min_le_left _ _))
  have hr1 : r ≤ 1 := (lt_of_lt_of_le hrlt ((min_le_right _ _).trans (min_le_right _ _))).le
  have h1 : P (E r)ᶜ ≤ ENNReal.ofReal (max C 0 * r ^ p) :=
    (hEb r hr hr₀').trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.rpow_nonneg hr.le p)))
  have h2 : P (F r)ᶜ ≤ ENNReal.ofReal (max D 0 * r ^ q) :=
    (hFb r hr hs₀').trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left D 0) (Real.rpow_nonneg hr.le q)))
  exact measure_compl_inter_le_polynomial P (E r) (F r) hr hr1 (le_max_right _ _) (le_max_right _ _) h1 h2

/-- An almost sure event is `PolyHighProb` (with `C = 0`). -/
theorem polyHighProb_const_of_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {G : Set Ω}
    (hG : ∀ᵐ ω ∂P, ω ∈ G) : PolyHighProb P (fun _ => G) := by
  unfold PolyHighProb
  refine ⟨1, one_pos, 0, 1, one_pos, fun r _ _ => ?_⟩
  have h0 : P Gᶜ = 0 := ae_iff.1 hG
  simp [h0]

/-- The gamma-only exponent `b_γ = 1/(2+γ)^2` of the verdict (not the `b` returned by `FrozenOneSidedBoundaryContinuity`). -/
theorem exponent_b_facts {γ : ℝ} (hγ : 0 < γ) :
    0 < 1 / (2 + γ) ^ 2 ∧ 1 / (2 + γ) ^ 2 < 1 ∧ 2 / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2 = 1 / (2 + γ) ^ 2 := by
  have h4 : (1 : ℝ) < (2 + γ) ^ 2 := by nlinarith
  refine ⟨by positivity, ?_, by ring⟩
  rw [div_lt_one (by positivity)]
  exact h4

/-- The radii of Lemma 3: `ρ < ρ₀ < ρ₁ < 1` and `(1+ρ₀)/2 = ρ₁`. -/
theorem scale_facts {ρ : ℝ} (hρ1 : ρ < 1) :
    ρ < (2 * ρ + 1) / 3 ∧ (2 * ρ + 1) / 3 < (ρ + 2) / 3 ∧ (ρ + 2) / 3 < 1 ∧
      (1 + (2 * ρ + 1) / 3) / 2 = (ρ + 2) / 3 := by
  refine ⟨by linarith, by linarith, by linarith, by ring⟩


/-! ## Part B: Lemma 3, `commonGood_fp36` (plan section 3) -/

/-- Smallness of a power: `ε^b < t` for all small `ε > 0`. -/
theorem rpow_lt_of_small {b t : ℝ} (hb : 0 < b) (ht : 0 < t) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → ε ^ b < t := by
  refine ⟨t ^ b⁻¹, Real.rpow_pos_of_pos ht _, fun ε hε hlt => ?_⟩
  calc ε ^ b < (t ^ b⁻¹) ^ b := Real.rpow_lt_rpow hε.le hlt hb
    _ = t := by rw [← Real.rpow_mul ht.le, inv_mul_cancel₀ hb.ne', Real.rpow_one]

/-- A disc `B_s(c)` inside `B_R(0)` satisfies `‖c‖ + s ≤ R` (a disc inside a disc, Armitage-Gardiner). -/
theorem norm_add_le_of_ball_subset {c : ℂ} {s R : ℝ} (hs : 0 < s) (hsub : ball c s ⊆ ball (0 : ℂ) R) :
    ‖c‖ + s ≤ R := by
  by_contra hlt
  have hlt' : R < ‖c‖ + s := not_le.1 hlt
  have hc : c ∈ ball (0 : ℂ) R := hsub (mem_ball_self hs)
  have hcn : ‖c‖ < R := by simpa [mem_ball] using hc
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg c) hcn
  rcases eq_or_ne c 0 with rfl | hc0
  · have hw : ((R : ℝ) : ℂ) ∈ ball (0 : ℂ) s := by
      rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg hR.le]
      simp only [norm_zero, zero_add] at hlt'
      exact hlt'
    have h' := hsub hw
    rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg hR.le] at h'
    exact lt_irrefl _ h'
  · have hcpos : 0 < ‖c‖ := norm_pos_iff.2 hc0
    have hcne : ‖c‖ ≠ 0 := hcpos.ne'
    have hnw : ‖((R / ‖c‖ : ℝ) : ℂ) * c‖ = R := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (div_nonneg hR.le hcpos.le)]
      field_simp
    have key : (R / ‖c‖ - 1) * ‖c‖ = R - ‖c‖ := by
      field_simp
    have habs : |R / ‖c‖ - 1| * ‖c‖ = R - ‖c‖ := by
      have h1 : |(R / ‖c‖ - 1) * ‖c‖| = |R / ‖c‖ - 1| * ‖c‖ := by
        rw [abs_mul, abs_of_pos hcpos]
      rw [← h1, key, abs_of_pos (sub_pos.2 hcn)]
    have hwc : ((R / ‖c‖ : ℝ) : ℂ) * c - c = (((R / ‖c‖ - 1 : ℝ)) : ℂ) * c := by
      push_cast
      ring
    have hdw : dist (((R / ‖c‖ : ℝ) : ℂ) * c) c < s := by
      rw [dist_eq_norm, hwc, norm_mul, Complex.norm_real, Real.norm_eq_abs, habs]
      linarith
    have h' := hsub (Metric.mem_ball.2 hdw)
    rw [mem_ball, dist_zero_right, hnw] at h'
    exact lt_irrefl _ h'

/-- `FiniteExitData` from finiteness: a finite set with consecutive edges and locally finite rows. -/
theorem finiteExitData_of_finite {m : ℤ → ℤ → ℕ} (hsucc : ∀ k : ℤ, m k (k + 1) ≠ 0)
    (hloc : IsLocallyFiniteMult m) {A : Set ℤ} (hA : A.Finite) : FiniteExitData m A := by
  unfold FiniteExitData
  exact ⟨hA, fun a _ => mdeg_pos_of_edge hloc (hsucc a), fun a ha => exists_vPath_to_boundary hsucc hA ha⟩

/-- **Lemma 3 core (plan section 3), at fixed `γ`, `b`, `ρ`, `ρ₀`, `ρ₁`.** The good event is the intersection of the
cell-size event (`CellSizeEstimateStmt` at `ζ = b`, radius `ρ₁`), the one-sided boundary event (`FrozenOneSidedBoundaryContinuity`
at radius `ρ₁`), the area-parametrization event and the regular-map event. -/
theorem fp36_good_core {𝒮 : SpaceFillingSLEModel} (h28 : CellSizeEstimateStmt 𝒮)
    (hm : MepsScalingInput 𝒮) (hBE : FrozenOneSidedBoundaryContinuity 𝒮)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {b ρ ρ₀ ρ₁ : ℝ}
    (hb : 0 < b) (hb1 : b < 1) (hbeq : 2 / (2 + γ) ^ 2 - b = b)
    (hρ0 : 0 < ρ) (hρρ₀ : ρ < ρ₀) (hρ₀ρ₁ : ρ₀ < ρ₁) (hρ₁1 : ρ₁ < 1) (hmid : (1 + ρ₀) / 2 = ρ₁)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (r : ℝ) (z y : ℂ) (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ) (hy : y ∈ ball z r) :
    ∃ ν A κ C₁ ε₀ : ℝ, 0 < ν ∧ 0 < A ∧ 0 < κ ∧ 0 ≤ C₁ ∧ 0 < ε₀ ∧
    ∃ G : ℝ → Set Ω, ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      0 < S.mε ε ∧ 8 * ε ^ b < r ∧ 64 * ε ^ b ≤ ε ^ (b / 2) ∧
      closure (ball z (r + 4 * ε ^ b)) ⊆ ball 0 ρ₀ ∧
      S.P (G ε)ᶜ ≤ ENNReal.ofReal (C₁ * ε ^ κ) ∧
      ∀ ω ∈ G ε, FP36GoodEnv S ρ₀ ρ₁ b ν A r z y ε ω := by
  have hρ₀0 : 0 < ρ₀ := by linarith
  have hρ₁0 : 0 < ρ₁ := by linarith
  have hρ₀1 : ρ₀ < 1 := by linarith
  obtain ⟨-, ν, A, -, -, hν, hA, -, hBEP⟩ := hBE γ hγ0 hγ2 ρ₁ hρ₁0 hρ₁1 Ω S hS
  let Ecell : ℝ → Set Ω := fun ε => {ω | ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 ρ₁).Nonempty →
      ε ^ (2 / (2 - γ) ^ 2 + b) ≤ diam (cell ε (S.η ω) k) ∧
        diam (cell ε (S.η ω) k) ≤ ε ^ (2 / (2 + γ) ^ 2 - b)}
  let Ebe : ℝ → Set Ω := fun ε => {ω | FP36OneSidedBEAt (S.mult ε ω) ε (S.η ω) ρ₁ ν A}
  let Area : Set Ω := {ω | IsAreaParametrized (S.μ ω) (S.η ω)}
  let Reg : Set Ω := {ω | ∀ ε : ℝ, 0 < ε → IsRegularMatedMap (S.mult ε ω) ε (S.η ω)}
  let G : ℝ → Set Ω := fun ε => (Ecell ε ∩ Ebe ε) ∩ (Area ∩ Reg)
  have hcellP : PolyHighProb S.P Ecell := h28 γ hγ0 hγ2 b ρ₁ hb hb1 hρ₁0 hρ₁1 Ω S hS
  have hbeP : PolyHighProb S.P Ebe := hBEP
  have harea : ∀ᵐ ω ∂S.P, ω ∈ Area := hS.isAreaParametrized
  have hreg : ∀ᵐ ω ∂S.P, ω ∈ Reg := ae_isRegularMatedMap (adjacentCellsMeetAeStep 𝒮) hγ0 hγ2 hS
  have hgood : PolyHighProb S.P G :=
    polyHighProb_inter (polyHighProb_inter hcellP hbeP)
      (polyHighProb_inter (polyHighProb_const_of_ae harea) (polyHighProb_const_of_ae hreg))
  obtain ⟨κ, hκ, C, r₀, hr₀, hPb⟩ := hgood
  obtain ⟨Cm, hCm, hmev⟩ := hm γ hγ0 hγ2
  obtain ⟨εm, hεm, hmS⟩ := hmev Ω S hS
  obtain ⟨δ1, hδ1, h1⟩ := rpow_lt_of_small hb (div_pos hr (by norm_num : (0 : ℝ) < 8))
  obtain ⟨δ2, hδ2, h2⟩ := rpow_lt_of_small (half_pos hb) (by norm_num : (0 : ℝ) < 1 / 64)
  have hd0 : 0 < r - dist y z := by
    rw [mem_ball] at hy
    linarith
  obtain ⟨δ3, hδ3, h3⟩ := rpow_lt_of_small hb hd0
  obtain ⟨δ4, hδ4, h4⟩ := rpow_lt_of_small hb (by linarith : (0 : ℝ) < (ρ₀ - ρ) / 4)
  have hnorm : ‖z‖ + r ≤ ρ := norm_add_le_of_ball_subset hr hball
  have hε₀ : 0 < min r₀ (min εm (min δ1 (min δ2 (min δ3 δ4)))) :=
    lt_min hr₀ (lt_min hεm (lt_min hδ1 (lt_min hδ2 (lt_min hδ3 hδ4))))
  refine ⟨ν, A, κ, max C 0, min r₀ (min εm (min δ1 (min δ2 (min δ3 δ4)))), hν, hA, hκ,
    le_max_right C 0, hε₀, G, ?_⟩
  intro ε hε hεε₀
  obtain ⟨hεr₀, hεrest⟩ := lt_min_iff.1 hεε₀
  obtain ⟨hεm', hεrest⟩ := lt_min_iff.1 hεrest
  obtain ⟨hε1, hεrest⟩ := lt_min_iff.1 hεrest
  obtain ⟨hε2, hεrest⟩ := lt_min_iff.1 hεrest
  obtain ⟨hε3, hε4⟩ := lt_min_iff.1 hεrest
  have hmpos : 0 < S.mε ε :=
    lt_of_lt_of_le (mul_pos (inv_pos.2 (by linarith)) (inv_pos.2 hε)) ((hmS ε hε hεm').1)
  have hδ8 : 8 * ε ^ b < r := by linarith [h1 ε hε hε1]
  have hsb : ε ^ b = ε ^ (b / 2) * ε ^ (b / 2) := by
    rw [← Real.rpow_add hε]
    congr 1
    ring
  have hs64 : 64 * ε ^ b ≤ ε ^ (b / 2) := by
    have hsn : 0 ≤ ε ^ (b / 2) := Real.rpow_nonneg hε.le _
    have hs1 : ε ^ (b / 2) < 1 / 64 := h2 ε hε hε2
    calc 64 * ε ^ b = (64 * ε ^ (b / 2)) * ε ^ (b / 2) := by rw [hsb]; ring
      _ ≤ 1 * ε ^ (b / 2) := mul_le_mul_of_nonneg_right (by linarith) hsn
      _ = ε ^ (b / 2) := one_mul _
  have hcl : closure (ball z (r + 4 * ε ^ b)) ⊆ ball 0 ρ₀ := by
    have h4' : ε ^ b < (ρ₀ - ρ) / 4 := h4 ε hε hε4
    refine (closure_ball_subset_closedBall).trans ?_
    intro w hw
    rw [mem_closedBall] at hw
    rw [mem_ball]
    have htri : dist w 0 ≤ dist w z + dist z 0 := dist_triangle w z 0
    have hz0 : dist z 0 = ‖z‖ := dist_zero_right z
    linarith
  have hprob : S.P (G ε)ᶜ ≤ ENNReal.ofReal (max C 0 * ε ^ κ) :=
    (hPb ε hε (lt_of_lt_of_le hεr₀ le_rfl)).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.rpow_nonneg hε.le κ)))
  refine ⟨hmpos, hδ8, hs64, hcl, hprob, ?_⟩
  intro ω hω
  obtain ⟨⟨hcellω, hbeω⟩, ⟨hareaω, hregω⟩⟩ := hω
  have hreg' : IsRegularMatedMap (S.mult ε ω) ε (S.η ω) := hregω ε hε
  have hsurj : Function.Surjective (S.η ω) := hareaω.2.2.1
  have hmesh : ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 ρ₁).Nonempty → diam (cell ε (S.η ω) k) ≤ ε ^ b := by
    intro k hk
    have := (hcellω k hk).2
    rwa [hbeq] at this
  have hmesh' : ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 ((1 + ρ₀) / 2)).Nonempty →
      diam (cell ε (S.η ω) k) ≤ ε ^ b := by
    rw [hmid]
    exact hmesh
  have hfe : ∀ U : Set ℂ, closure U ⊆ ball 0 ρ₀ →
      FiniteExitData (S.mult ε ω) (cellVertices ε (S.η ω) U) ∧
      FiniteExitData (S.mult ε ω) (interiorCellVertices ε (S.η ω) U) := by
    intro U hU
    have hUb : Bornology.IsBounded U := isBounded_ball.subset (subset_closure.trans hU)
    have hfin : (cellVertices ε (S.η ω) U).Finite :=
      cellVertices_finite_of_proper hreg'.continuous hreg'.proper hε hUb
    have hint : (interiorCellVertices ε (S.η ω) U).Finite :=
      hfin.subset (fun x hx => (show x ∈ cellVertices ε (S.η ω) U \ cellVertices ε (S.η ω) (frontier U) from hx).1)
    exact ⟨finiteExitData_of_finite hreg'.succ hreg'.locallyFinite hfin,
      finiteExitData_of_finite hreg'.succ hreg'.locallyFinite hint⟩
  have hballρ₀ : ball z r ⊆ ball 0 ρ₀ := hball.trans (Metric.ball_subset_ball hρρ₀.le)
  have hmarg : dist y z + ε ^ b < r := by linarith [h3 ε hε hε3]
  have hint0 : vertexOf ε (S.η ω) y ∈ interiorCellVertices ε (S.η ω) (ball z r) :=
    TruncatedLaws.vertexOf_mem_interiorCellVertices_of_mesh hreg'.continuous hsurj hreg'.proper hε
      hballρ₀ hρ₀1 hy hmesh' hmarg
  unfold FP36GoodEnv
  dsimp only
  exact ⟨hareaω, fun j k hjk => hreg'.cells_meet j k hjk, hmesh, hfe, hint0, hbeω⟩

/-- **Lemma 3 (`commonGood_fp36`, plan CHATGPT-221 section 3): the common polynomially good environment.** The exponent
is the gamma-only `b = 1/(2+γ)^2` of the verdict (not the `b` of `FrozenOneSidedBoundaryContinuity`), and `CellSizeEstimateStmt`
is used at `ζ = b`, so that its upper diameter exponent `2/(2+γ)^2 - ζ` equals `b`. -/
theorem commonGood_fp36 {𝒮 : SpaceFillingSLEModel}
    (h28 : CellSizeEstimateStmt 𝒮) (hm : MepsScalingInput 𝒮)
    (hBE : FrozenOneSidedBoundaryContinuity 𝒮) :
    ∀ γ : ℝ, 0 < γ → γ < 2 →
    ∃ b : ℝ, 0 < b ∧
    ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
    ∀ y ∈ ball z r,
    let ρ₀ := (2 * ρ + 1) / 3
    let ρ₁ := (ρ + 2) / 3
    ρ < ρ₀ ∧ ρ₀ < ρ₁ ∧ ρ₁ < 1 ∧
    ∃ ν A κ C₁ ε₀ : ℝ,
      0 < ν ∧ 0 < A ∧ 0 < κ ∧ 0 ≤ C₁ ∧ 0 < ε₀ ∧
    ∃ G : ℝ → Set Ω,
    ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      let δ := ε ^ b
      let s := ε ^ (b / 2)
      0 < S.mε ε ∧
      8 * δ < r ∧
      64 * δ ≤ s ∧
      closure (ball z (r + 4 * δ)) ⊆ ball 0 ρ₀ ∧
      S.P (G ε)ᶜ ≤ ENNReal.ofReal (C₁ * ε ^ κ) ∧
      ∀ ω ∈ G ε,
        FP36GoodEnv S ρ₀ ρ₁ b ν A r z y ε ω := by
  intro γ hγ0 hγ2
  obtain ⟨hb, hb1, hbeq⟩ := exponent_b_facts hγ0
  refine ⟨1 / (2 + γ) ^ 2, hb, fun ρ hρ0 hρ1 Ω _ S hS r z hr hball y hy => ?_⟩
  obtain ⟨s1, s2, s3, s4⟩ := scale_facts hρ1
  exact ⟨s1, s2, s3, fp36_good_core h28 hm hBE hγ0 hγ2 hb hb1 hbeq hρ0 s1 s2 s3 s4 S hS r z y hr hball hy⟩


#print axioms MatedCRT.FirstPass36.commonGood_fp36

end FirstPass36
end MatedCRT
