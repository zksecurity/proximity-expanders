module

public import LDPC.PaperLemmas.ExpansionCounting

/-! Review layout: Helpers.ExpansionDistance. Declaration names are unchanged. -/

@[expose] public section

open scoped BigOperators

namespace SmoothLDPC

/-- A unique parity-check neighbour of the support of an error must reject it.
This is the algebraic step used in the weighted unique-neighbor argument. -/
theorem unique_neighbor_detects
    {L R 𝔽 : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    [Field 𝔽] [DecidableEq 𝔽]
    {G : TannerGraph L R} (H : G.WeightedSystem 𝔽) (e : L → 𝔽) (j : R)
    (hj : j ∈ G.uniqueNeighbors (support e)) :
    H.check e j ≠ 0 := by
  rw [TannerGraph.mem_uniqueNeighbors] at hj
  obtain ⟨i, hsingle⟩ := Finset.card_eq_one.mp hj
  have hi : i ∈ G.left j ∩ support e := by simp [hsingle]
  obtain ⟨hiG, hie⟩ := Finset.mem_inter.mp hi
  simp only [TannerGraph.WeightedSystem.check]
  have hzero : ∀ k ∈ G.left j, k ≠ i → e k = 0 := by
    intro k hk hki
    by_contra hk0
    have hmem : k ∈ G.left j ∩ support e := by simp [hk, hk0]
    simp [hsingle, hki] at hmem
  rw [Finset.sum_eq_single i]
  · exact mul_ne_zero (H.weight_ne_zero i j hiG) ((mem_support e i).mp hie)
  · intro k hk hki
    simp [hzero k hk hki]
  · exact fun h => (h hiG).elim

/-! ## Original distance with an explicit integer expansion cutoff -/

section ImprovedDistance
variable {L R F : Type*} [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R] [Field F] [DecidableEq F]
    {G : TannerGraph L R} {c k K : ℕ} {γ δ : ℚ}

theorem nonzero_codeword_large (hG : G.IsExpander c k γ δ)
    (hc : 0 < c) (hγ : γ < 1 / 2) (H : G.WeightedSystem F)
    {x : L → F} (hx : x ∈ H.code) (hx0 : x ≠ 0) :
    δ * Fintype.card L < ((support x).card : ℚ) := by
  by_contra h
  have hu := proposition_4 hG (support x) (le_of_not_gt h)
  have hp : 0 < (support x).card :=
    Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr
      (fun he => hx0 ((support_eq_empty_iff x).mp he)))
  have hfactor : (0 : ℚ) < (1 - 2 * γ) * c :=
    mul_pos (by linarith) (by exact_mod_cast hc)
  have hpos : 0 < (G.uniqueNeighbors (support x)).card := by
    have := mul_pos hfactor (show (0 : ℚ) < (support x).card by exact_mod_cast hp)
    exact_mod_cast lt_of_lt_of_le this hu
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
  exact unique_neighbor_detects H x j hj ((mem_code H x).mp hx j)

theorem neighborhood_card_le (hreg : G.IsRegular c k) (S : Finset L) :
    (G.neighborhood S).card ≤ c * S.card := by
  calc
    _ ≤ ∑ i ∈ S, (G.right i).card := Finset.card_biUnion_le
    _ = _ := by simp [hreg.left_degree, Nat.mul_comm]

theorem unique_subset_neighborhood (S : Finset L) :
    G.uniqueNeighbors S ⊆ G.neighborhood S := by
  intro j hj
  have hp : 0 < (G.left j ∩ S).card := by
    rw [(G.mem_uniqueNeighbors S j).mp hj]; decide
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hp
  exact (G.mem_neighborhood S j).mpr
    ⟨i, (Finset.mem_inter.mp hi).2, (Finset.mem_inter.mp hi).1⟩

/-- A unique neighbor of a partial support must meet its complement or be
one of the removed checks. Used for both original and punctured distance. -/
theorem unique_subset_removed (H : G.WeightedSystem F) {R₀ : Finset R} {x : L → F}
    (hx : x ∈ H.relaxedCode R₀) (S : Finset L) (hS : S ⊆ support x) :
    G.uniqueNeighbors S ⊆ R₀ ∪ G.neighborhood (support x \ S) := by
  intro j hj
  by_contra hn
  have hjR₀ : j ∉ R₀ := fun h => hn (Finset.mem_union_left _ h)
  have hinter : G.left j ∩ support x = G.left j ∩ S := by
    ext i
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨hi, hix⟩
      refine ⟨hi, ?_⟩
      by_contra hiS
      exact hn (Finset.mem_union_right _ ((G.mem_neighborhood _ _).mpr
        ⟨i, Finset.mem_sdiff.mpr ⟨hix, hiS⟩, hi⟩))
    · exact fun ⟨hi, hiS⟩ => ⟨hi, hS hiS⟩
  apply unique_neighbor_detects H x j _ (hx j hjR₀)
  rw [G.mem_uniqueNeighbors, hinter]
  exact (G.mem_uniqueNeighbors S j).mp hj


end ImprovedDistance

end SmoothLDPC
