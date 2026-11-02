module

public import LDPC.Helpers.Algebra

/-! Review layout: PaperLemmas.ExpansionCounting. Declaration names are unchanged. -/

@[expose] public section

open scoped BigOperators

namespace SmoothLDPC

section UniqueNeighbors
variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    {G : TannerGraph L R} {c k : ℕ} {γ δ : ℚ}

/-- Unique-neighbor property: a non-unique neighbor consumes at least two edges. -/
theorem proposition_4 (hG : G.IsExpander c k γ δ) (S : Finset L)
    (hS : (S.card : ℚ) ≤ δ * Fintype.card L) :
    (1 - 2 * γ) * c * S.card ≤ (G.uniqueNeighbors S).card := by
  have hpoint (j : R) :
      (if j ∈ G.neighborhood S then 2 else 0) ≤
        (G.left j ∩ S).card + if (G.left j ∩ S).card = 1 then 1 else 0 := by
    have hpos : j ∈ G.neighborhood S ↔ 0 < (G.left j ∩ S).card := by
      simp [Finset.card_pos, Finset.Nonempty, and_comm]
    simp only [hpos]
    split_ifs <;> omega
  have hcount : 2 * (G.neighborhood S).card ≤ c * S.card + (G.uniqueNeighbors S).card := by
    simpa [-TannerGraph.mem_neighborhood, Finset.sum_add_distrib, Finset.sum_ite, G.incidence_sum S,
      hG.left_degree, TannerGraph.uniqueNeighbors, Nat.mul_comm] using
      Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset R)) => hpoint j)
  have hcountQ : (2 : ℚ) * (G.neighborhood S).card ≤
      c * S.card + (G.uniqueNeighbors S).card := by exact_mod_cast hcount
  have hexp := hG.expansion S hS
  nlinarith

end UniqueNeighbors

end SmoothLDPC
