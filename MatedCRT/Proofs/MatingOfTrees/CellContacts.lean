/- Adapted from Leonardo Bonanno's lean-formalizations, source module
   MatedCRTHarmonic.RouteM.DLevels at commit 31e7483. -/
import MatedCRT.Proofs.MatingOfTrees.ConsecutiveCells

/-!
# Contact times for cells joined by the boundary-length criterion

The level window can be a singleton when the mesh is chosen from the path. The last and
first contacts still exist in the closed cell intervals and the path stays above their level.
-/

namespace MatedCRT

open Set

/-- Contact times on the two outer intervals at a level below the middle interval. -/
theorem exists_level_contacts {X : ℝ → ℝ} (hX : Continuous X) {a b c d lev : ℝ}
    (hbc : b ≤ c) {s₀ s₁ : ℝ} (hs₀ : s₀ ∈ Icc a b) (hs₁ : s₁ ∈ Icc c d)
    (h₀ : X s₀ ≤ lev) (h₁ : X s₁ ≤ lev)
    (hmid : ∀ t ∈ Icc b c, lev ≤ X t) :
    ∃ p₁ ∈ Icc a b, ∃ p₂ ∈ Icc c d, X p₁ = lev ∧ X p₂ = lev ∧
      ∀ t ∈ Ioo p₁ p₂, lev ≤ X t := by
  have hXb : lev ≤ X b := hmid b ⟨le_rfl, hbc⟩
  have hXc : lev ≤ X c := hmid c ⟨hbc, le_rfl⟩
  let A₁ : Set ℝ := {s | s ≤ b ∧ X s ≤ lev}
  have hA₁c : IsClosed A₁ := isClosed_Iic.inter (isClosed_Iic.preimage hX)
  have hs₀A : s₀ ∈ A₁ := ⟨hs₀.2, h₀⟩
  have hA₁b : BddAbove A₁ := ⟨b, fun _ hs => hs.1⟩
  let p₁ : ℝ := sSup A₁
  have hp₁A : p₁ ∈ A₁ := hA₁c.csSup_mem ⟨s₀, hs₀A⟩ hA₁b
  have hs₀p₁ : s₀ ≤ p₁ := le_csSup hA₁b hs₀A
  have hXp₁ : X p₁ = lev := by
    obtain ⟨s, hs, hXs⟩ := intermediate_value_Icc hp₁A.1 hX.continuousOn ⟨hp₁A.2, hXb⟩
    have hsA : s ∈ A₁ := ⟨hs.2, hXs.le⟩
    have hsle : s ≤ p₁ := le_csSup hA₁b hsA
    rw [← le_antisymm hsle hs.1]
    exact hXs
  let A₂ : Set ℝ := {s | c ≤ s ∧ X s ≤ lev}
  have hA₂c : IsClosed A₂ := isClosed_Ici.inter (isClosed_Iic.preimage hX)
  have hs₁A : s₁ ∈ A₂ := ⟨hs₁.1, h₁⟩
  have hA₂b : BddBelow A₂ := ⟨c, fun _ hs => hs.1⟩
  let p₂ : ℝ := sInf A₂
  have hp₂A : p₂ ∈ A₂ := hA₂c.csInf_mem ⟨s₁, hs₁A⟩ hA₂b
  have hp₂s₁ : p₂ ≤ s₁ := csInf_le hA₂b hs₁A
  have hXp₂ : X p₂ = lev := by
    obtain ⟨s, hs, hXs⟩ := intermediate_value_Icc' hp₂A.1 hX.continuousOn ⟨hp₂A.2, hXc⟩
    have hsA : s ∈ A₂ := ⟨hs.1, hXs.le⟩
    have hles : p₂ ≤ s := csInf_le hA₂b hsA
    rw [← le_antisymm hs.2 hles]
    exact hXs
  refine ⟨p₁, ⟨hs₀.1.trans hs₀p₁, hp₁A.1⟩, p₂, ⟨hp₂A.1, hp₂s₁.trans hs₁.2⟩,
    hXp₁, hXp₂, ?_⟩
  intro t ht
  by_contra hn
  have hle : X t ≤ lev := le_of_lt (lt_of_not_ge hn)
  rcases le_or_gt t b with htb | hbt
  · have ht₁ : t ≤ p₁ := le_csSup hA₁b ⟨htb, hle⟩
    linarith [ht.1]
  rcases le_or_gt t c with htc | hct
  · exact hn (hmid t ⟨hbt.le, htc⟩)
  · have ht₂ : p₂ ≤ t := csInf_le hA₂b ⟨hct.le, hle⟩
    linarith [ht.2]

/-- The boundary-minimum condition yields intersecting cells under the merge rule. -/
theorem cells_meet_of_bmAdjacent {ε : ℝ} (hε : 0 ≤ ε) {X : ℝ → ℝ}
    (hX : Continuous X) {η : ℝ → ℂ}
    (hdistinct : ∀ x y, x ≠ y → IsLocalMin X x → IsLocalMin X y → X x ≠ X y)
    (hmerge : ∀ s t, MatedCRTHarmonic.MatedCRT.DirectRel X s t → η s = η t)
    {j k : ℤ} (hjk : j < k) (hadj : bmAdjacent ε X j k) :
    (cell ε η j ∩ cell ε η k).Nonempty := by
  have hab : ε * j - ε ≤ ε * j := by linarith
  have hcd : ε * k - ε ≤ ε * k := by linarith
  have hjk' : (j : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast (show j + 1 ≤ k by omega)
  have hbc : ε * j ≤ ε * k - ε := by nlinarith
  let m₀ := sInf (X '' Icc (ε * j - ε) (ε * j))
  let m₁ := sInf (X '' Icc (ε * k - ε) (ε * k))
  let m := max m₀ m₁
  have hK₀ : IsCompact (X '' Icc (ε * j - ε) (ε * j)) := isCompact_Icc.image hX
  have hK₁ : IsCompact (X '' Icc (ε * k - ε) (ε * k)) := isCompact_Icc.image hX
  obtain ⟨s₀, hs₀, hXs₀⟩ := hK₀.sInf_mem ((nonempty_Icc.mpr hab).image X)
  obtain ⟨s₁, hs₁, hXs₁⟩ := hK₁.sInf_mem ((nonempty_Icc.mpr hcd).image X)
  have h₀ : X s₀ ≤ m := by rw [hXs₀]; exact le_max_left _ _
  have h₁ : X s₁ ≤ m := by rw [hXs₁]; exact le_max_right _ _
  have hmid : ∀ t ∈ Icc (ε * j) (ε * k - ε), m ≤ X t := by
    intro t ht
    exact hadj.trans (csInf_le (isCompact_Icc.image hX).bddBelow ⟨t, ht, rfl⟩)
  obtain ⟨p₁, hp₁, p₂, hp₂, hp₁v, hp₂v, habove⟩ :=
    exists_level_contacts hX hbc hs₀ hs₁ h₀ h₁ hmid
  have hp : p₁ ≤ p₂ := hp₁.2.trans (hbc.trans hp₂.1)
  have hη := merge_of_level_interval hdistinct hmerge hp hp₁v hp₂v habove
  refine ⟨η p₁, ⟨p₁, ?_, rfl⟩, ⟨p₂, ?_, hη.symm⟩⟩
  · simpa only [cell, mul_sub, mul_one] using hp₁
  · simpa only [cell, mul_sub, mul_one] using hp₂

/-- A nonzero edge count joins intersecting cells when both coordinates obey the merge rule. -/
theorem cells_meet_of_bmEdgeCount {ε : ℝ} (hε : 0 ≤ ε) {L R : ℝ → ℝ} {η : ℝ → ℂ}
    (hL : Continuous L) (hR : Continuous R)
    (hLd : ∀ x y, x ≠ y → IsLocalMin L x → IsLocalMin L y → L x ≠ L y)
    (hRd : ∀ x y, x ≠ y → IsLocalMin R x → IsLocalMin R y → R x ≠ R y)
    (hLm : ∀ s t, MatedCRTHarmonic.MatedCRT.DirectRel L s t → η s = η t)
    (hRm : ∀ s t, MatedCRTHarmonic.MatedCRT.DirectRel R s t → η s = η t)
    {j k : ℤ} (hedge : bmEdgeCount ε L R j k ≠ 0) :
    (cell ε η j ∩ cell ε η k).Nonempty := by
  have ordered : ∀ j k : ℤ, j < k → bmEdgeCount ε L R j k ≠ 0 →
      (cell ε η j ∩ cell ε η k).Nonempty := by
    intro j k hjk hne
    have hside : bmAdjacent ε L j k ∨ bmAdjacent ε R j k := by
      by_contra hn
      apply hne
      simp [bmEdgeCount, ne_of_lt hjk, min_eq_left hjk.le, max_eq_right hjk.le, hn]
    rcases hside with hside | hside
    · exact cells_meet_of_bmAdjacent hε hL hLd hLm hjk hside
    · exact cells_meet_of_bmAdjacent hε hR hRd hRm hjk hside
  rcases lt_trichotomy j k with hjk | h | hkj
  · exact ordered j k hjk hedge
  · subst k
    exact False.elim (hedge (bmEdgeCount_self ε L R j))
  · have h := ordered k j hkj (by rwa [bmEdgeCount_symm])
    simpa only [inter_comm] using h

end MatedCRT
