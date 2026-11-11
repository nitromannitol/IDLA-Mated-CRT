import MatedCRT.FirstPass.S2h.Cutoff

/-!
# Restricted integrals over unions of balls as countable suprema

For a family `B : ℕ → Set ℂ` of open sets contained in the unit ball and a set `S`
of indices, the union `V = ⋃ i ∈ S, B i` is the increasing union of the finite unions `⋃ i ∈ J, B i`, `J ⊆ S` finite.
Hence for a measurable nonnegative `f`, `∫_V f dν` is the supremum over finite `J ⊆ S` of `∫_{U_J} f dν`, and each
of these is the supremum over `n` of the cutoff integrals of `Cutoff.lean`.
-/

namespace MatedCRT

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- Nonempty complement of a union of open subsets of the unit ball (the point `2` is outside). -/
theorem compl_nonempty_of_subset_ball {U : Set ℂ} (hU : U ⊆ ball (0 : ℂ) 1) : Uᶜ.Nonempty := by
  refine ⟨2, fun h => ?_⟩
  have h2 : (2 : ℂ) ∈ ball (0 : ℂ) 1 := hU h
  rw [mem_ball_zero_iff] at h2
  norm_num at h2

/-- Monotone convergence over finite subfamilies: the integral over the union
of the sets with index in `S` is the supremum of the integrals over the finite subunions. -/
theorem lintegral_restrict_iUnion_eq_iSup {ν : Measure ℂ} (B : ℕ → Set ℂ) (hO : ∀ i, IsOpen (B i)) (S : Set ℕ)
    {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x in (⋃ i ∈ S, B i), f x ∂ν =
      ⨆ J : {J : Finset ℕ // ↑J ⊆ S}, ∫⁻ x in (⋃ i ∈ J.1, B i), f x ∂ν := by
  have hmeasU : ∀ J : {J : Finset ℕ // ↑J ⊆ S}, MeasurableSet (⋃ i ∈ J.1, B i) := fun J =>
    (isOpen_biUnion fun i _ => hO i).measurableSet
  have hV : MeasurableSet (⋃ i ∈ S, B i) := (isOpen_biUnion fun i _ => hO i).measurableSet
  have hsubV : ∀ J : {J : Finset ℕ // ↑J ⊆ S}, (⋃ i ∈ J.1, B i) ⊆ ⋃ i ∈ S, B i := fun J x hx => by
    obtain ⟨i, hiJ, hxi⟩ := mem_iUnion₂.1 hx
    exact mem_iUnion₂.2 ⟨i, J.2 hiJ, hxi⟩
  have hpt : ∀ x, (⨆ J : {J : Finset ℕ // ↑J ⊆ S}, (⋃ i ∈ J.1, B i).indicator f x) =
      (⋃ i ∈ S, B i).indicator f x := by
    intro x
    by_cases hx : x ∈ ⋃ i ∈ S, B i
    · obtain ⟨i, hiS, hxi⟩ := mem_iUnion₂.1 hx
      rw [indicator_of_mem hx]
      apply le_antisymm
      · exact iSup_le fun J => indicator_le_self _ _ x
      · have hsing : (↑({i} : Finset ℕ) : Set ℕ) ⊆ S := by
          simpa using hiS
        refine le_iSup_of_le ⟨{i}, hsing⟩ ?_
        rw [indicator_of_mem (mem_iUnion₂.2 ⟨i, Finset.mem_singleton_self i, hxi⟩)]
    · rw [indicator_of_notMem hx]
      have h0 : ∀ J : {J : Finset ℕ // ↑J ⊆ S}, (⋃ i ∈ J.1, B i).indicator f x = 0 := fun J =>
        indicator_of_notMem (fun h => hx (hsubV J h)) _
      simp [h0]
  have hdir : Directed (· ≤ ·) (fun J : {J : Finset ℕ // ↑J ⊆ S} => (⋃ i ∈ J.1, B i).indicator f) := by
    intro J₁ J₂
    have hU : (↑(J₁.1 ∪ J₂.1) : Set ℕ) ⊆ S := by
      push_cast
      exact Set.union_subset J₁.2 J₂.2
    refine ⟨⟨J₁.1 ∪ J₂.1, hU⟩, ?_, ?_⟩
    · intro x
      refine indicator_le_indicator_of_subset ?_ (fun _ => zero_le) x
      intro y hy
      obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.1 hy
      exact mem_iUnion₂.2 ⟨i, Finset.mem_union_left _ hi, hyi⟩
    · intro x
      refine indicator_le_indicator_of_subset ?_ (fun _ => zero_le) x
      intro y hy
      obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.1 hy
      exact mem_iUnion₂.2 ⟨i, Finset.mem_union_right _ hi, hyi⟩
  have hmeas : ∀ J : {J : Finset ℕ // ↑J ⊆ S}, Measurable ((⋃ i ∈ J.1, B i).indicator f) := fun J =>
    hf.indicator (hmeasU J)
  calc ∫⁻ x in (⋃ i ∈ S, B i), f x ∂ν = ∫⁻ x, (⋃ i ∈ S, B i).indicator f x ∂ν :=
        (lintegral_indicator hV f).symm
    _ = ∫⁻ x, ⨆ J : {J : Finset ℕ // ↑J ⊆ S}, (⋃ i ∈ J.1, B i).indicator f x ∂ν := by
        simp_rw [hpt]
    _ = ⨆ J : {J : Finset ℕ // ↑J ⊆ S}, ∫⁻ x, (⋃ i ∈ J.1, B i).indicator f x ∂ν :=
        lintegral_iSup_directed_of_measurable hmeas hdir
    _ = ⨆ J : {J : Finset ℕ // ↑J ⊆ S}, ∫⁻ x in (⋃ i ∈ J.1, B i), f x ∂ν := by
        refine iSup_congr fun J => ?_
        exact lintegral_indicator (hmeasU J) f

/-- The restricted integral over a union of unit-ball subsets is the double supremum over finite subfamilies `J ⊆ S`
and cutoff levels `n`: the code coordinates `∫ θ_{J,n} f dν` suffice. -/
theorem lintegral_restrict_iUnion_eq_iSup_cutoff {ν : Measure ℂ} (B : ℕ → Set ℂ) (hO : ∀ i, IsOpen (B i))
    (hB : ∀ i, B i ⊆ ball (0 : ℂ) 1) (S : Set ℕ) {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x in (⋃ i ∈ S, B i), f x ∂ν =
      ⨆ J : {J : Finset ℕ // ↑J ⊆ S}, ⨆ n : ℕ,
        ∫⁻ x, ENNReal.ofReal (cutoffBall (⋃ i ∈ J.1, B i) n x) * f x ∂ν := by
  have hsub : ∀ J : Finset ℕ, (⋃ i ∈ J, B i) ⊆ ball (0 : ℂ) 1 := fun J =>
    iUnion₂_subset fun i _ => hB i
  rw [lintegral_restrict_iUnion_eq_iSup B hO S hf]
  refine iSup_congr fun J => ?_
  exact lintegral_restrict_open_eq_iSup (isOpen_biUnion fun i _ => hO i)
    (compl_nonempty_of_subset_ball (hsub J.1)) hf

end MatedCRT
