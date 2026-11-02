module

public import LDPC.Helpers.CheckSampling
public import LDPC.PaperLemmas.Folding
public import LDPC.Helpers.ExpansionParameters
public import Mathlib.Algebra.Order.Floor.Ring

/-! Shared-neighborhood sampling: no separate coordinate queries are needed. -/
@[expose] public section
open scoped ProbabilityTheory
namespace SmoothLDPC.Protocol
attribute [local instance] Classical.propDecidable

variable {L R F : Type} [Fintype L] [DecidableEq L] [Nonempty L]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Field F] [DecidableEq F] [Fintype F] {G : TannerGraph L R}

omit [Fintype F] [DecidableEq F] [Nonempty L] [Nonempty R] in
/-- Honest codewords pass the parity and consistency tests on every sampled neighborhood. -/
theorem shared_accept_honest (H : G.WeightedSystem F) (u v : L → F)
    (hu : u ∈ H.code) (hv : v ∈ H.code) (r : F) {Q : ℕ} (sample : Fin Q → R) :
    SharedAccept H u v (fun z => u + z • v) r sample := by
  have hucheck : H.check u = 0 := hu
  have hvcheck : H.check v = 0 := hv
  refine ⟨?_, H.code.add_mem hu (H.code.smul_mem r hv), ?_⟩
  · simp [MCA.parityAccept, TannerGraph.WeightedSystem.badChecks, hucheck, hvcheck]
  · intro q i hi
    rfl

omit [Fintype F] [Nonempty L] in
/-- Outside the close-fold event, a neighborhood query detects a mismatch
with the guaranteed check fraction. -/
theorem shared_response_probability_le (H : G.WeightedSystem F) {ρ α : ℚ}
    (hα : α ≤ 1)
    (hdetect : ∀ S : Finset L, ρ ≤ S.card → α * Fintype.card R ≤ (G.neighborhood S).card)
    (u v : L → F) (response : F → L → F) (r : F) (Q : ℕ) :
    Pr_{let sample ← $ᵖ (Fin Q → R)}[SharedAccept H u v response r sample] ≤
      (if GoodFold H.code ρ u v r then 1 else 0) +
        ENNReal.ofReal (1 - (α : ℝ))^Q := by
  classical
  by_cases hg : GoodFold H.code ρ u v r
  · simp only [hg, if_true]
    exact (Probability.prob_le_one _ _).trans le_self_add
  · simp only [hg, if_false, zero_add]
    by_cases hc : response r ∈ H.code
    · have hfar : ρ ≤ (distance (u + r • v) (response r) : ℚ) := by
        by_contra hn
        exact hg ⟨response r, hc, lt_of_not_ge hn⟩
      let S := support (u + r • v - response r)
      refine (Probability.Pr_le_Pr_of_implies ($ᵖ (Fin Q → R))
        (fun sample => SharedAccept H u v response r sample)
        (fun sample => ∀ q, sample q ∈ Finset.univ \ G.neighborhood S) ?_).trans
        (miss_checks_le _ α hα (hdetect S hfar) Q)
      intro sample h q
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hj
      obtain ⟨i, hi, hij⟩ := (G.mem_neighborhood S _).mp hj
      have hne : u i + r * v i ≠ response r i := by
        simpa [S, mem_support, sub_eq_zero, smul_eq_mul] using hi
      exact hne (h.2.2 q i hij)
    · rw [Probability.prob_eq_zero_of_forall_not ($ᵖ (Fin Q → R))
        (fun sample => SharedAccept H u v response r sample) (fun _ h => hc h.2.1)]
      positivity

omit [Fintype F] [DecidableEq F] [Nonempty L] in
/-- When many input checks fail, the shared verifier must miss that same set. -/
theorem shared_acceptance_le_of_many (H : G.WeightedSystem F) {α : ℚ}
    (hα : α ≤ 1) (u v : L → F)
    (hb : α * Fintype.card R ≤ (H.badChecks u v).card)
    (response : F → L → F) (r : F) (Q : ℕ) :
    Pr_{let sample ← $ᵖ (Fin Q → R)}[SharedAccept H u v response r sample] ≤
      ENNReal.ofReal (1 - (α : ℝ))^Q := by
  exact (Probability.Pr_le_Pr_of_implies ($ᵖ (Fin Q → R))
    (fun sample => SharedAccept H u v response r sample)
    (fun sample => ∀ q, sample q ∈ Finset.univ \ H.badChecks u v)
    (fun _ h => h.1)).trans (miss_checks_le _ α hα hb Q)

omit [Field F] [DecidableEq F] [Fintype F] [Nonempty L] [Nonempty R] in
/-- Expansion on a subset of size ceil(rho) controls every larger mismatch set.
The generic statement retains its ceiling hypothesis; Paper.check_sampling derives it from the margin. -/
theorem neighborhood_detection_of_expansion {c k : ℕ} {γ δ ρ α : ℚ}
    (hG : G.IsExpander c k γ δ) (hγ : γ ≤ 1)
    (hceil : (Nat.ceil ρ : ℚ) ≤ δ * Fintype.card L)
    (hα : α * Fintype.card R ≤ (1 - γ) * c * ρ)
    (S : Finset L) (hS : ρ ≤ S.card) :
    α * Fintype.card R ≤ (G.neighborhood S).card := by
  have hs : Nat.ceil ρ ≤ S.card := Nat.ceil_le.mpr hS
  obtain ⟨S₀, hsub, hcard⟩ := Finset.exists_subset_card_eq hs
  have hexp := hG.expansion S₀ (by simpa [hcard] using hceil)
  have hmono : G.neighborhood S₀ ⊆ G.neighborhood S := by
    intro j hj
    obtain ⟨i, hi, hij⟩ := (G.mem_neighborhood S₀ j).mp hj
    exact (G.mem_neighborhood S j).mpr ⟨i, hsub hi, hij⟩
  have hsize : ((G.neighborhood S₀).card : ℚ) ≤ (G.neighborhood S).card := by
    exact_mod_cast Finset.card_le_card hmono
  calc
    _ ≤ (1 - γ) * c * ρ := hα
    _ ≤ (1 - γ) * c * Nat.ceil ρ :=
      mul_le_mul_of_nonneg_left (Nat.le_ceil ρ) (mul_nonneg (sub_nonneg.mpr hγ) (by positivity))
    _ ≤ (G.neighborhood S₀).card := by simpa [hcard] using hexp
    _ ≤ _ := hsize

omit [Field F] [DecidableEq F] [Fintype F] [Nonempty L] [Nonempty R] in
/-- Each sampled check opens k interleaved coordinates; reuse can only lower the count. -/
theorem openedCoordinates_card_le {c k Q : ℕ} (hreg : G.IsRegular c k)
    (sample : Fin Q → R) : (openedCoordinates G sample).card ≤ k * Q := by
  apply (Finset.card_biUnion_le).trans
  simp [hreg.right_degree, Nat.mul_comm]

end SmoothLDPC.Protocol
