module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.LinearAlgebra.Pi

/-!
# Definitions for weighted expander codes

Definitions for *On Proximity Gaps for Expander Codes*.

Distances, puncturing budgets, and surviving distances are absolute counts.
The expander radius `δ` is relative. Original distance uses an explicit integer
cutoff; the smoothness and folding statements use the paper's margin `γδn ≥ 1`.
-/

@[expose] public section

open scoped BigOperators

namespace SmoothLDPC

variable {L R F : Type*}

/-- A finite bipartite parity-check graph. -/
structure TannerGraph (L R : Type*) [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R] where
  right : L → Finset R
  left : R → Finset L
  mem_left_iff : ∀ i j, i ∈ left j ↔ j ∈ right i

namespace TannerGraph
variable [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

def neighborhood (G : TannerGraph L R) (S : Finset L) : Finset R :=
  S.biUnion G.right

def uniqueNeighbors (G : TannerGraph L R) (S : Finset L) : Finset R :=
  Finset.univ.filter fun j => (G.left j ∩ S).card = 1

structure IsRegular (G : TannerGraph L R) (c k : ℕ) : Prop where
  left_degree : ∀ i, (G.right i).card = c
  right_degree : ∀ j, (G.left j).card = k

/-- Positivity and parameter ranges are hypotheses of the results
that use them, rather than implicit conventions. -/
structure IsExpander (G : TannerGraph L R) (c k : ℕ) (γ δ : ℚ) : Prop
    extends G.IsRegular c k where
  expansion : ∀ S : Finset L, (S.card : ℚ) ≤ δ * Fintype.card L →
    (1 - γ) * c * S.card ≤ (G.neighborhood S).card

/-- Every edge has a nonzero field coefficient. -/
structure WeightedSystem (G : TannerGraph L R) (F : Type*) [Field F] where
  weight : L → R → F
  weight_ne_zero : ∀ i j, i ∈ G.left j → weight i j ≠ 0

namespace WeightedSystem
variable [Field F] {G : TannerGraph L R}

def check (H : G.WeightedSystem F) (x : L → F) (j : R) : F :=
  ∑ i ∈ G.left j, H.weight i j * x i

/-- Checks form a linear map, so all deleted-check codes below are submodules. -/
def checkMap (H : G.WeightedSystem F) : (L → F) →ₗ[F] (R → F) where
  toFun := H.check
  map_add' x y := by
    funext j
    simp [check, mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    funext j
    simp [check, mul_left_comm, ← Finset.mul_sum]

def code (H : G.WeightedSystem F) : Submodule F (L → F) := H.checkMap.ker

/-- Remove the checks in `R₀`, retaining all original coordinates. -/
def relaxedCode (H : G.WeightedSystem F) (R₀ : Finset R) : Submodule F (L → F) where
  carrier := {x | ∀ j, j ∉ R₀ → H.check x j = 0}
  zero_mem' := by simp [check]
  add_mem' {x y} hx hy j hj := by
    change H.checkMap (x + y) j = 0
    simp only [map_add, Pi.add_apply]
    simp [checkMap, hx j hj, hy j hj]
  smul_mem' a {x} hx j hj := by
    change H.checkMap (a • x) j = 0
    simp [map_smul, hx j hj, checkMap]

noncomputable def badChecks (H : G.WeightedSystem F) (u v : L → F) : Finset R := by
  classical
  exact Finset.univ.filter fun j => H.check u j ≠ 0 ∨ H.check v j ≠ 0

end WeightedSystem
end TannerGraph

section Distances
variable [Fintype L] [Field F] [DecidableEq F]

def support (x : L → F) : Finset L := Finset.univ.filter fun i => x i ≠ 0

/-- Absolute Hamming distance. -/
def distance (x y : L → F) : ℕ := (support (x - y)).card

/-- A coordinate counts once if either column differs. -/
def pairDistance [DecidableEq L] (u v cu cv : L → F) : ℕ :=
  (support (u - cu) ∪ support (v - cv)).card

/-- Minimum distance at least `D`, expressed without a minimum over an empty
set. For a linear code it suffices to consider nonzero codewords. -/
def HasDistance (C : Submodule F (L → F)) (D : ℚ) : Prop :=
  ∀ x ∈ C, x ≠ 0 → D ≤ ((support x).card : ℚ)

/-- Joint farness Δ((u,v),C²)>P uses the coordinate-wise interleaved distance. -/
def PairFar [DecidableEq L] (C : Submodule F (L → F)) (P : ℚ)
    (u v : L → F) : Prop :=
  ∀ cu ∈ C, ∀ cv ∈ C, P < (pairDistance u v cu cv : ℚ)

/-- The strict folding event in the main and technical folding statements. -/
def GoodFold (C : Submodule F (L → F)) (D : ℚ) (u v : L → F) (r : F) : Prop :=
  ∃ cw ∈ C, (distance (u + r • v) cw : ℚ) < D

end Distances

section Puncturing
variable [Field F]

/-- Restriction retains the coordinates in `I`. -/
def restrict (I : Finset L) : (L → F) →ₗ[F] (I → F) :=
  LinearMap.funLeft F F (fun i : I => (i : L))

/-- Actual puncturing: the image under restriction, with existential completions. -/
def puncture (C : Submodule F (L → F)) (I : Finset L) : Submodule F (I → F) :=
  C.map (restrict I)

end Puncturing

/-- Smoothness: a single coordinate deletion set works for every word of
the relaxed code, and is chosen before the folding seed. -/
def IsSmooth [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    [Field F] [DecidableEq F] {G : TannerGraph L R}
    (H : G.WeightedSystem F) (α P D : ℚ) : Prop :=
  ∀ R₀ : Finset R, (R₀.card : ℚ) ≤ α * Fintype.card R →
    ∃ L₀ : Finset L, (L₀.card : ℚ) ≤ P ∧
      HasDistance (puncture (H.relaxedCode R₀) (Finset.univ \ L₀)) D

end SmoothLDPC
