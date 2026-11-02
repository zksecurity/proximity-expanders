module

public import LDPC.Statements.MCA
public import LDPC.Helpers.Algebra

/-! Smoothness to ArkLib's exact, closed-radius MCA event and parity-query soundness. -/
@[expose] public section
open scoped BigOperators ProbabilityTheory
namespace SmoothLDPC
namespace MCA
open CoreDefinitions LinearCode

variable {L R F : Type} [Fintype L] [DecidableEq L]
    [Field F] [DecidableEq F] [Fintype F]

omit [Fintype F] in
/-- Large agreement gives the closed absolute Hamming bound. -/
theorem close_of_agreement [Nonempty L] (ρ : ℚ) (w c : L → F) (T : Finset L)
    (hT : (T.card:ℝ)≥Fintype.card L*(1-(ρ:ℝ)/Fintype.card L))
    (hag : ∀ i∈T,w i=c i) : (distance w c:ℚ)≤ρ := by
  have hdis : Disjoint (support (w-c)) T := by
    rw [Finset.disjoint_left]
    intro i hi hiT
    exact (mem_support _ _).mp hi (by simp [hag i hiT])
  have hc : (support (w-c)).card+T.card≤Fintype.card L := by
    rw [← Finset.card_union_of_disjoint hdis]
    exact Finset.card_le_univ _
  have hc' : ((support (w-c)).card:ℝ)+T.card≤Fintype.card L := by exact_mod_cast hc
  have hn : (Fintype.card L:ℝ)≠0 := by positivity
  have hsize : (Fintype.card L:ℝ)*(1-(ρ:ℝ)/Fintype.card L)=Fintype.card L-ρ := by field_simp
  rw [hsize] at hT
  have h : ((support (w-c)).card:ℝ)≤ρ := by linarith
  exact_mod_cast h

/-- MCA failure supplies an actual codeword at closed radius rho. -/
theorem nearby_of_bad [Nonempty L] (C : Submodule F (L → F)) (ρ : ℚ) (u v : L → F) (z : F)
    (h : Bad C ρ u v z) : ∃ c∈C,(distance (u+z • v) c:ℚ)≤ρ := by
  obtain ⟨T,hT,hfold,_⟩ := h
  obtain ⟨c,hc,heq⟩ := (mem_projectedCodeSubmod_iff _ _ _).mp hfold
  refine ⟨c,hc,close_of_agreement ρ _ _ T hT ?_⟩
  intro i hi
  simpa [projectedWord,AffineLineGenerator] using congrFun heq ⟨i,hi⟩

variable [Fintype R] [DecidableEq R] {G : TannerGraph L R}

end MCA
end SmoothLDPC
