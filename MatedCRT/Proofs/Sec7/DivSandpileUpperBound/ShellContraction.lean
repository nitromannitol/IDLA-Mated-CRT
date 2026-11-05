import MatedCRT.Draft.Section7
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBoundDiv.Visit
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBoundDiv.Reduction
import MatedCRT.Proofs.Sec7.MassBoundOdometer.Comparison
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.CrudeCells

/-! Comparison of the walk events in the shell contraction argument. -/

namespace MatedCRT.Sec7

open MeasureTheory Set

/-- A cell which meets an open set without meeting its frontier lies entirely
inside the open set. -/
theorem cell_subset_open_of_meets_avoids_frontier
    {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) {O : Set ℂ} (hO : IsOpen O)
    {a : ℤ} (ha : a ∈ cellVertices ε η O)
    (hfront : a ∉ cellVertices ε η (frontier O)) : cell ε η a ⊆ O := by
  intro z hz
  by_contra hzO
  obtain ⟨w, hwa, hwO⟩ := ha
  obtain ⟨p, hpa, hpfront⟩ := ConstantOrderDiv.preconnected_inter_frontier_nonempty
    (ConstantOrderDiv.cell_isPreconnected' hη a) hO ⟨w, hwa, hwO⟩ ⟨z, hz, hzO⟩
  exact hfront ⟨p, hpa, hpfront⟩

/-- Frontier cells separate the graph vertices whose cells lie on the two
sides of an open set. -/
theorem boundary_inside_cells_subset_frontier_cells
    {m : ℤ → ℤ → ℕ} {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η)
    {O : Set ℂ} (hO : IsOpen O)
    (hadj : ∀ a b, m a b ≠ 0 → (cell ε η a ∩ cell ε η b).Nonempty) :
    vBoundary m (cellVertices ε η O \ cellVertices ε η (frontier O)) ⊆
      cellVertices ε η (frontier O) := by
  intro b hb
  obtain ⟨hbout, a, ha, hab⟩ := hb
  obtain ⟨z, hza, hzb⟩ := hadj a b hab
  have hzO := cell_subset_open_of_meets_avoids_frontier hη hO ha.1 ha.2 hza
  have hbO : b ∈ cellVertices ε η O := ⟨z, hzb, hzO⟩
  by_contra hbF
  exact hbout ⟨hbO, hbF⟩

/-- Frontier cells of an intermediate thickening lie in the annulus between
the original cell set and a strictly larger thickening. -/
theorem frontier_cells_subset_thickened_annulus
    {ε r s : ℝ} {η : ℝ → ℂ} {Θ : Set ℤ} (hr : 0 < r) (hrs : r < s) :
    cellVertices ε η (frontier (Metric.thickening r (fillCells ε η Θ))) ⊆
      cellVertices ε η (Metric.thickening s (fillCells ε η Θ)) \ Θ := by
  intro a ha
  obtain ⟨z, hza, hzfront⟩ := ha
  have hzouter : z ∈ Metric.thickening s (fillCells ε η Θ) :=
    (Metric.cthickening_subset_thickening' (lt_trans hr hrs) hrs _)
      (Metric.closure_thickening_subset_cthickening r _ (frontier_subset_closure hzfront))
  refine ⟨⟨z, hza, hzouter⟩, ?_⟩
  intro haΘ
  have hzinner : z ∈ Metric.thickening r (fillCells ε η Θ) :=
    Metric.self_subset_thickening hr _ (mem_iUnion₂.mpr ⟨a, haΘ, hza⟩)
  rw [Metric.isOpen_thickening.frontier_eq] at hzfront
  exact hzfront.2 hzinner

/-- A bound on the odometer on the frontier cells bounds the next shell's
graph-boundary maximum, provided the next shell contains the inner cells. -/
theorem next_shell_boundary_odometer_le_frontier
    {m : ℤ → ℤ → ℕ} {ε ρ t M : ℝ} {η : ℝ → ℂ} {O : Set ℂ} {Θnext : Set ℤ}
    (hε : 0 < ε) (ht : 0 < t) (hM : 0 ≤ M) (hη : Continuous η) (hO : IsOpen O)
    (hsymm : ∀ a b, m a b = m b a) (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hsucc : ∀ k : ℤ, m k (k + 1) ≠ 0)
    (hadj : ∀ a b, m a b ≠ 0 → (cell ε η a ∩ cell ε η b).Nonempty)
    (hfin : (cellVertices ε η (Metric.closedBall 0 ρ)).Finite)
    (hlap : ∀ a ∈ matedDiscreteCluster m ε η ρ t, a ≠ 0 →
      matedLaplacian m (stoppedOdometer m ε η ρ t) a = ((matedDeg m a : ℕ) : ℝ)⁻¹)
    (hI : (cellVertices ε η O \ cellVertices ε η (frontier O)).Finite)
    (h0 : (0 : ℤ) ∈ cellVertices ε η O \ cellVertices ε η (frontier O))
    (hnext : cellVertices ε η O \ cellVertices ε η (frontier O) ⊆ Θnext)
    (hfront : ∀ b ∈ cellVertices ε η (frontier O), stoppedOdometer m ε η ρ t b ≤ M) :
    (⨆ b : vBoundary m Θnext, stoppedOdometer m ε η ρ t b) ≤ M := by
  have hinner : (⨆ b : vBoundary m (cellVertices ε η O \ cellVertices ε η (frontier O)),
      stoppedOdometer m ε η ρ t b) ≤ M := by
    apply Real.iSup_le
    · intro b
      exact hfront b (boundary_inside_cells_subset_frontier_cells hη hO hadj b.property)
    · exact hM
  apply Real.iSup_le
  · intro b
    have hb : (b : ℤ) ∉ cellVertices ε η O \ cellVertices ε η (frontier O) :=
      fun hb => b.property.1 (hnext hb)
    exact (stoppedOdometer_le_iSup_vBoundary hε ht hsymm hlf hsucc hfin hlap hI h0 hb).trans hinner
  · exact hM

/-- A positive Euclidean thickening of filled cells contains the graph closure
when adjacent cells meet. -/
theorem graph_closure_subset_thickened_cell_vertices
    {m : ℤ → ℤ → ℕ} {ε r : ℝ} {η : ℝ → ℂ} {Θ : Set ℤ}
    (hε : 0 ≤ ε) (hr : 0 < r)
    (hadj : ∀ a b, m a b ≠ 0 → (cell ε η a ∩ cell ε η b).Nonempty) :
    vClosure m Θ ⊆ cellVertices ε η (Metric.thickening r (fillCells ε η Θ)) := by
  intro a ha
  rcases ha with ha | ⟨_, b, hb, hba⟩
  · have hz := vertexPoint_mem_own_cell hε η a
    exact ⟨vertexPoint ε η a, hz, Metric.self_subset_thickening hr _
      (mem_iUnion₂.mpr ⟨a, ha, hz⟩)⟩
  · obtain ⟨z, hzb, hza⟩ := hadj b a hba
    exact ⟨z, hza, Metric.self_subset_thickening hr _ (mem_iUnion₂.mpr ⟨b, hb, hzb⟩)⟩

/-- Removing the inner thickening keeps an annulus disjoint from the graph
closure of its preceding shell. -/
theorem thickened_annulus_disjoint_graph_closure
    {m : ℤ → ℤ → ℕ} {ε r : ℝ} {η : ℝ → ℂ} {Θ E : Set ℤ}
    (hε : 0 ≤ ε) (hr : 0 < r)
    (hadj : ∀ a b, m a b ≠ 0 → (cell ε η a ∩ cell ε η b).Nonempty) :
    E \ cellVertices ε η (Metric.thickening r (fillCells ε η Θ)) ⊆ (vClosure m Θ)ᶜ := by
  intro a ha hac
  exact ha.2 (graph_closure_subset_thickened_cell_vertices hε hr hadj hac)

/-- If an annulus avoids the graph closure of the previous shell, its graph
boundary avoids the previous shell itself. -/
theorem annulus_boundary_disjoint_previous_shell
    {m : ℤ → ℤ → ℕ} (hsymm : ∀ a b, m a b = m b a)
    {B Θ : Set ℤ} (hB : B ⊆ (vClosure m Θ)ᶜ) :
    vBoundary m B ⊆ Θᶜ := by
  intro b hb hbΘ
  obtain ⟨hbB, a, haB, hab⟩ := hb
  have haΘ : a ∉ Θ := fun ha => hB haB (Or.inl ha)
  have haBd : a ∈ vBoundary m Θ := ⟨haΘ, b, hbΘ, by simpa [hsymm a b] using hab⟩
  exact hB haB (Or.inr haBd)

/-- The annulus boundary maximum is controlled by the previous shell boundary
maximum by the discrete maximum principle. -/
theorem annulus_boundary_odometer_le_previous
    {m : ℤ → ℤ → ℕ} {ε ρ t : ℝ} {η : ℝ → ℂ} {B Θ : Set ℤ}
    (hε : 0 < ε) (ht : 0 < t) (hsymm : ∀ a b, m a b = m b a)
    (hlf : ∀ a, {b | m a b ≠ 0}.Finite) (hsucc : ∀ k : ℤ, m k (k + 1) ≠ 0)
    (hfin : (cellVertices ε η (Metric.closedBall 0 ρ)).Finite)
    (hlap : ∀ a ∈ matedDiscreteCluster m ε η ρ t, a ≠ 0 →
      matedLaplacian m (stoppedOdometer m ε η ρ t) a = ((matedDeg m a : ℕ) : ℝ)⁻¹)
    (hΘ : Θ.Finite) (h0 : (0 : ℤ) ∈ Θ) (hB : B ⊆ (vClosure m Θ)ᶜ) :
    (⨆ b : vBoundary m B, stoppedOdometer m ε η ρ t b) ≤
      ⨆ b : vBoundary m Θ, stoppedOdometer m ε η ρ t b := by
  apply Real.iSup_le
  · intro b
    exact stoppedOdometer_le_iSup_vBoundary hε ht hsymm hlf hsucc hfin hlap hΘ h0
      (annulus_boundary_disjoint_previous_shell hsymm hB b.property)
  · exact Real.iSup_nonneg fun b => stoppedOdometer_nonneg hε ht b

/-- A path which exits `B` before hitting `B \ Λ` remains in `A` up to its
exit, provided `A` contains the occupied part of `B`. -/
theorem exit_before_hit_subset_survival (B Λ A : Set ℤ) (hA : B ∩ Λ ⊆ A) :
    {x : ℕ → ℤ | vExitTime B x < vHitTime (B \ Λ) x} ⊆
      {x | ∀ n : ℕ, (n : ℕ∞) < vExitTime B x → x n ∈ A} := by
  intro x hx n hn
  have hnB : x n ∈ B := (ConstantOrderDiv.lt_vExitTime_iff'.1 hn) n le_rfl
  have hnHit : (n : ℕ∞) < vHitTime (B \ Λ) x := lt_trans hn hx
  have hncompl : x n ∉ B \ Λ := by
    have := (ConstantOrderDiv.lt_vExitTime_iff'.1 hnHit) n le_rfl
    exact this
  have hnΛ : x n ∈ Λ := by
    by_contra hnΛ
    exact hncompl ⟨hnB, hnΛ⟩
  exact hA ⟨hnB, hnΛ⟩

/-- The survival-probability bound of Lemma 6.8 also bounds the strict
exit-before-hit probability appearing in Lemma 7.3. -/
theorem exit_before_hit_probability_le (m : ℤ → ℤ → ℕ) (b : ℤ)
    (B Λ A : Set ℤ) (q : ℝ) (hq : 0 ≤ q) (hA : B ∩ Λ ⊆ A)
    (hprob : srwLaw m b {x | ∀ n : ℕ, (n : ℕ∞) < vExitTime B x → x n ∈ A} ≤
      ENNReal.ofReal q) :
    (srwLaw m b {x | vExitTime B x < vHitTime (B \ Λ) x}).toReal ≤ q := by
  have hle := (measure_mono (exit_before_hit_subset_survival B Λ A hA)).trans hprob
  have hreal := ENNReal.toReal_mono (by simp : ENNReal.ofReal q ≠ ⊤) hle
  simpa [ENNReal.toReal_ofReal hq] using hreal

/-- Pointwise contraction of the stopped odometer from the walk estimate and
the odometer bound on an annulus. -/
theorem stopped_odometer_le_of_survival_bound
    (m : ℤ → ℤ → ℕ) (ε ρ t : ℝ) (η : ℝ → ℂ)
    (B A : Set ℤ) (b : ℤ) (M q : ℝ) (hM : 0 ≤ M) (hq : 0 ≤ q)
    (hA : B ∩ matedDiscreteCluster m ε η ρ t ⊆ A)
    (hodo : stoppedOdometer m ε η ρ t b ≤ M *
      (srwLaw m b {x | vExitTime B x <
        vHitTime (B \ matedDiscreteCluster m ε η ρ t) x}).toReal)
    (hprob : srwLaw m b {x | ∀ n : ℕ, (n : ℕ∞) < vExitTime B x → x n ∈ A} ≤
      ENNReal.ofReal q) :
    stoppedOdometer m ε η ρ t b ≤ M * q := by
  exact hodo.trans (mul_le_mul_of_nonneg_left
    (exit_before_hit_probability_le m b B (matedDiscreteCluster m ε η ρ t) A q hq hA hprob) hM)

/-- The walk estimate and the maximum principle bound the annulus odometer by
the previous shell's boundary maximum times the survival probability. -/
theorem stopped_odometer_le_previous_boundary_of_survival_bound
    {m : ℤ → ℤ → ℕ} {ε ρ t q : ℝ} {η : ℝ → ℂ} {B Θ A : Set ℤ} {b : ℤ}
    (hε : 0 < ε) (ht : 0 < t) (hq : 0 ≤ q) (hsymm : ∀ a b, m a b = m b a)
    (hlf : ∀ a, {b | m a b ≠ 0}.Finite) (hsucc : ∀ k : ℤ, m k (k + 1) ≠ 0)
    (hfin : (cellVertices ε η (Metric.closedBall 0 ρ)).Finite)
    (hlap : ∀ a ∈ matedDiscreteCluster m ε η ρ t, a ≠ 0 →
      matedLaplacian m (stoppedOdometer m ε η ρ t) a = ((matedDeg m a : ℕ) : ℝ)⁻¹)
    (hΘ : Θ.Finite) (h0 : (0 : ℤ) ∈ Θ) (hB : B ⊆ (vClosure m Θ)ᶜ)
    (hA : B ∩ matedDiscreteCluster m ε η ρ t ⊆ A)
    (hodo : stoppedOdometer m ε η ρ t b ≤
      (⨆ c : vBoundary m B, stoppedOdometer m ε η ρ t c) *
        (srwLaw m b {x | vExitTime B x <
          vHitTime (B \ matedDiscreteCluster m ε η ρ t) x}).toReal)
    (hprob : srwLaw m b {x | ∀ n : ℕ, (n : ℕ∞) < vExitTime B x → x n ∈ A} ≤
      ENNReal.ofReal q) :
    stoppedOdometer m ε η ρ t b ≤
      (⨆ c : vBoundary m Θ, stoppedOdometer m ε η ρ t c) * q := by
  have hM : 0 ≤ ⨆ c : vBoundary m B, stoppedOdometer m ε η ρ t c :=
    Real.iSup_nonneg fun c => stoppedOdometer_nonneg hε ht c
  exact (stopped_odometer_le_of_survival_bound m ε ρ t η B A b _ q hM hq hA hodo hprob).trans
    (mul_le_mul_of_nonneg_right
      (annulus_boundary_odometer_le_previous hε ht hsymm hlf hsucc hfin hlap hΘ h0 hB) hq)

/-- A survival estimate on the separating frontier contracts the next shell's
boundary odometer maximum relative to the preceding shell. -/
theorem next_shell_boundary_contracts_of_survival_bound
    {m : ℤ → ℤ → ℕ} {ε ρ t q : ℝ} {η : ℝ → ℂ} {B Θ A Θnext : Set ℤ} {O : Set ℂ}
    (hε : 0 < ε) (ht : 0 < t) (hq : 0 ≤ q) (hη : Continuous η) (hO : IsOpen O)
    (hsymm : ∀ a b, m a b = m b a) (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hsucc : ∀ k : ℤ, m k (k + 1) ≠ 0)
    (hadj : ∀ a b, m a b ≠ 0 → (cell ε η a ∩ cell ε η b).Nonempty)
    (hfin : (cellVertices ε η (Metric.closedBall 0 ρ)).Finite)
    (hlap : ∀ a ∈ matedDiscreteCluster m ε η ρ t, a ≠ 0 →
      matedLaplacian m (stoppedOdometer m ε η ρ t) a = ((matedDeg m a : ℕ) : ℝ)⁻¹)
    (hΘ : Θ.Finite) (h0 : (0 : ℤ) ∈ Θ) (hB : B ⊆ (vClosure m Θ)ᶜ)
    (hA : B ∩ matedDiscreteCluster m ε η ρ t ⊆ A)
    (hI : (cellVertices ε η O \ cellVertices ε η (frontier O)).Finite)
    (hI0 : (0 : ℤ) ∈ cellVertices ε η O \ cellVertices ε η (frontier O))
    (hnext : cellVertices ε η O \ cellVertices ε η (frontier O) ⊆ Θnext)
    (hodo : ∀ b ∈ cellVertices ε η (frontier O), stoppedOdometer m ε η ρ t b ≤
      (⨆ c : vBoundary m B, stoppedOdometer m ε η ρ t c) *
        (srwLaw m b {x | vExitTime B x <
          vHitTime (B \ matedDiscreteCluster m ε η ρ t) x}).toReal)
    (hprob : ∀ b ∈ cellVertices ε η (frontier O),
      srwLaw m b {x | ∀ n : ℕ, (n : ℕ∞) < vExitTime B x → x n ∈ A} ≤ ENNReal.ofReal q) :
    (⨆ b : vBoundary m Θnext, stoppedOdometer m ε η ρ t b) ≤
      (⨆ b : vBoundary m Θ, stoppedOdometer m ε η ρ t b) * q := by
  have hM : 0 ≤ (⨆ b : vBoundary m Θ, stoppedOdometer m ε η ρ t b) * q :=
    mul_nonneg (Real.iSup_nonneg fun b => stoppedOdometer_nonneg hε ht b) hq
  apply next_shell_boundary_odometer_le_frontier hε ht hM hη hO hsymm hlf hsucc hadj hfin hlap hI hI0 hnext
  intro b hb
  exact stopped_odometer_le_previous_boundary_of_survival_bound hε ht hq hsymm hlf hsucc
    hfin hlap hΘ h0 hB hA (hodo b hb) (hprob b hb)

/-- Lemma 7.3 and a survival bound imply pointwise odometer contraction on the
annulus, simultaneously for all admissible scales and annuli. -/
theorem stopped_odometer_le_of_survival_bound_ae
    (𝒮 : SpaceFillingSLEModel) (hodo : OdometerBoundMassStmt 𝒮)
    (γ ρ : ℝ) (hγ : 0 < γ) (hγ' : γ < 2) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ ε t : ℝ, 0 < ε → 0 < t → ∀ (B A : Set ℤ) (b : ℤ) (q : ℝ),
      B ⊆ cellVertices ε (S.η ω) (Metric.ball 0 ρ) \ {0} → b ∈ B → 0 ≤ q →
      0 ≤ (⨆ c : vBoundary (S.mult ε ω) B,
        stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t c) →
      B ∩ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t ⊆ A →
      srwLaw (S.mult ε ω) b {x | ∀ n : ℕ, (n : ℕ∞) < vExitTime B x → x n ∈ A} ≤
        ENNReal.ofReal q →
      stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t b ≤
        (⨆ c : vBoundary (S.mult ε ω) B,
          stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t c) * q := by
  filter_upwards [hodo γ hγ hγ' ρ hρ hρ' Ω S hS] with ω hω
  intro ε t hε ht B A b q hB hb hq hM hA hprob
  exact stopped_odometer_le_of_survival_bound (S.mult ε ω) ε ρ t (S.η ω) B A b _ q
    hM hq hA (hω ε t hε ht B hB b hb) hprob

end MatedCRT.Sec7
