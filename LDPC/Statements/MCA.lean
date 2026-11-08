module

public import LDPC.Statements.Core
public import ArkLib.Data.CodingTheory.ProximityGenerator.Basic
public import Mathlib.Tactic.FinCases
public import ArkLib.Data.Probability.Instances

/-! Public definitions and review interfaces: Statements.MCA. -/

@[expose] public section

open scoped BigOperators ProbabilityTheory
namespace SmoothLDPC
namespace MCA
open CoreDefinitions LinearCode

variable {L R F : Type} [Fintype L] [DecidableEq L]
    [Field F] [DecidableEq F] [Fintype F]

/-- ArkLib's canonical MCA failure event, at an absolute rational radius. -/
def Bad (C : Submodule F (L → F)) (ρ : ℚ) (u v : L → F) (z : F) : Prop :=
  IsMCA (AffineLineGenerator F) C z ![u,v] ((ρ:ℝ)/Fintype.card L)

variable [Fintype R] [DecidableEq R] {G : TannerGraph L R}

end MCA
end SmoothLDPC

open scoped BigOperators ProbabilityTheory
namespace SmoothLDPC.MCA

variable {L R F : Type} [Fintype L] [DecidableEq L]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Field F] [Fintype F] [DecidableEq F] {G : TannerGraph L R}

/-- Every sampled check passes on both fixed input columns. -/
def parityAccept (H : G.WeightedSystem F) (u v : L → F) {Q : ℕ} (sample : Fin Q → R) : Prop :=
  ∀ i,sample i∈Finset.univ \ H.badChecks u v


/-- The few-check guarantee and the query-augmented guarantee, uniformly over inputs. -/
def Guarantees (H : G.WeightedSystem F) (ρ : ℚ) (p t : ℕ) : Prop :=
  letI := SampleableType.ofFintype F; letI := SampleableType.ofFintype R
  (∀ u v : L → F,(H.badChecks u v).card≤t →
    Pr{let z ← $ᵗ F}[Bad H.code ρ u v z]≤(max 1 p:ℕ)/(Fintype.card F:ENNReal)) ∧
  (∀ (u v : L → F) (Q : ℕ),
    Pr{let z ← $ᵗ F;let sample ← $ᵗ (Fin Q → R)}[
      parityAccept H u v sample ∧ Bad H.code ρ u v z]≤
      max ((max 1 p:ℕ)/(Fintype.card F:ENNReal))
        ((((Fintype.card R-t:ℕ):ENNReal)/Fintype.card R)^Q))


end SmoothLDPC.MCA
