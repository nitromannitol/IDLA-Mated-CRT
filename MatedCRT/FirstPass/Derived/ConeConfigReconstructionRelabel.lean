import MatedCRT.FirstPass.Derived.GMS21LocalCellConfiguration

/-!
# Local configurations are invariant under order-preserving relabeling

If the labels of the local vertices of `d` are carried by a strictly increasing map `f` onto those
of `d'`, with the same points and multiplicities, then the local configurations of `d` and `d'`
coincide.
-/

namespace MatedCRT

theorem mem_localVertices_iff {V : Set ℂ} {d : (ℤ → ℂ) × (ℤ → ℤ → ℕ)} {y : ℤ} :
    y ∈ localVertices V d ↔ d.1 y ∈ V ∨ ∃ x, d.1 x ∈ V ∧ d.2 x y ≠ 0 :=
  Iff.rfl

/-- The `k`-th element of the image of a finset under a map strictly increasing on it is the image
of the `k`-th element. -/
theorem orderEmbOfFin_image {F : Finset ℤ} {f : ℤ → ℤ} (hf : StrictMonoOn f F)
    (h : (F.image f).card = F.card) (i : Fin F.card) :
    (F.image f).orderEmbOfFin h i = f (F.orderEmbOfFin rfl i) := by
  symm
  have := Finset.orderEmbOfFin_unique (s := F.image f) h (f := fun i => f (F.orderEmbOfFin rfl i))
    (fun i => Finset.mem_image_of_mem f (F.orderEmbOfFin_mem rfl i))
    (fun i j hij => hf (F.orderEmbOfFin_mem rfl i) (F.orderEmbOfFin_mem rfl j)
      ((F.orderEmbOfFin rfl).strictMono hij))
  exact congrFun this i

theorem localConfigOf_image {F : Finset ℤ} {f : ℤ → ℤ} {d d' : (ℤ → ℂ) × (ℤ → ℤ → ℕ)}
    (hf : StrictMonoOn f F) (hpt : ∀ y ∈ F, d'.1 (f y) = d.1 y)
    (hmult : ∀ x ∈ F, ∀ y ∈ F, d'.2 (f x) (f y) = d.2 x y) :
    localConfigOf (F.image f) d' = localConfigOf F d := by
  have hc : (F.image f).card = F.card := Finset.card_image_of_injOn hf.injOn
  have hcast : ∀ (n : ℕ) (h : (F.image f).card = n) (k : ℕ) (hk : k < n)
      (hk' : k < (F.image f).card),
      (F.image f).orderEmbOfFin rfl ⟨k, hk'⟩ = (F.image f).orderEmbOfFin h ⟨k, hk⟩ := by
    intro n h
    subst h
    intros
    rfl
  refine Prod.ext hc (Prod.ext ?_ ?_)
  · funext k
    show (if hk : k < (F.image f).card then d'.1 ((F.image f).orderEmbOfFin rfl ⟨k, hk⟩) else 0) =
      if hk : k < F.card then d.1 (F.orderEmbOfFin rfl ⟨k, hk⟩) else 0
    by_cases hk : k < F.card
    · have hk' : k < (F.image f).card := hc ▸ hk
      rw [dite_eq_left hk, dite_eq_left hk', hcast _ hc k hk hk', orderEmbOfFin_image hf hc]
      exact hpt _ (F.orderEmbOfFin_mem rfl _)
    · rw [dite_eq_right hk, dite_eq_right (hc ▸ hk)]
  · funext k l
    show (if hk : k < (F.image f).card then
        if hl : l < (F.image f).card then
          d'.2 ((F.image f).orderEmbOfFin rfl ⟨k, hk⟩) ((F.image f).orderEmbOfFin rfl ⟨l, hl⟩)
        else 0
      else 0) =
      if hk : k < F.card then
        if hl : l < F.card then d.2 (F.orderEmbOfFin rfl ⟨k, hk⟩) (F.orderEmbOfFin rfl ⟨l, hl⟩)
        else 0
      else 0
    by_cases hk : k < F.card
    · by_cases hl : l < F.card
      · have hk' : k < (F.image f).card := hc ▸ hk
        have hl' : l < (F.image f).card := hc ▸ hl
        rw [dite_eq_left hk, dite_eq_left hl, dite_eq_left hk', dite_eq_left hl',
          hcast _ hc k hk hk', hcast _ hc l hl hl', orderEmbOfFin_image hf hc,
          orderEmbOfFin_image hf hc]
        exact hmult _ (F.orderEmbOfFin_mem rfl _) _ (F.orderEmbOfFin_mem rfl _)
      · rw [dite_eq_left hk, dite_eq_left (hc ▸ hk), dite_eq_right hl, dite_eq_right (hc ▸ hl)]
    · rw [dite_eq_right hk, dite_eq_right (hc ▸ hk)]

/-- **Local configurations are invariant under order-preserving relabeling**: if a map `f` strictly
increasing on the local vertices of `d` carries them onto those of `d'` and preserves points and
multiplicities, then `d` and `d'` have the same local configuration. -/
theorem localConfig_eq_of_strictMonoOn {V : Set ℂ} {d d' : (ℤ → ℂ) × (ℤ → ℤ → ℕ)} {f : ℤ → ℤ}
    (hf : StrictMonoOn f (localVertices V d)) (hloc : localVertices V d' = f '' localVertices V d)
    (hpt : ∀ y ∈ localVertices V d, d'.1 (f y) = d.1 y)
    (hmult : ∀ x ∈ localVertices V d, ∀ y ∈ localVertices V d, d'.2 (f x) (f y) = d.2 x y) :
    localConfig V d' = localConfig V d := by
  by_cases hfin : (localVertices V d).Finite
  · have hfin' : (localVertices V d').Finite := hloc ▸ hfin.image f
    have hF : localFinset V d = hfin.toFinset := dite_eq_left hfin
    have hF' : localFinset V d' = hfin.toFinset.image f := by
      rw [localFinset, dite_eq_left hfin']
      ext y
      simp [hloc]
    have hmem : ∀ y, y ∈ hfin.toFinset ↔ y ∈ localVertices V d := fun y => hfin.mem_toFinset
    have hs : ∀ y ∈ hfin.toFinset, y ∈ localVertices V d := fun y hy => (hmem y).1 hy
    unfold localConfig
    rw [hF, hF']
    refine localConfigOf_image ?_ (fun y hy => hpt y (hs y hy))
      (fun x hx y hy => hmult x (hs x hx) y (hs y hy))
    intro a ha b hb hab
    exact hf (hs a ha) (hs b hb) hab
  · have hinf' : ¬ (localVertices V d').Finite := by
      rw [hloc]
      exact (Set.Infinite.image hf.injOn hfin)
    have h1 : localFinset V d = ∅ := dite_eq_right hfin
    have h2 : localFinset V d' = ∅ := dite_eq_right hinf'
    unfold localConfig
    rw [h1, h2]
    simp [localConfigOf]

/-- Local configurations only depend on the points and multiplicities on the local vertices. -/
theorem localConfig_congr {V : Set ℂ} {d d' : (ℤ → ℂ) × (ℤ → ℤ → ℕ)}
    (hloc : localVertices V d' = localVertices V d) (hpt : ∀ y ∈ localVertices V d, d'.1 y = d.1 y)
    (hmult : ∀ x ∈ localVertices V d, ∀ y ∈ localVertices V d, d'.2 x y = d.2 x y) :
    localConfig V d' = localConfig V d :=
  localConfig_eq_of_strictMonoOn (f := id) strictMonoOn_id (by simpa using hloc) hpt hmult

end MatedCRT
