/-
Copyright 2026 Tatsuhiko Takimoto.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import FormalConjecturesUtil
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Set.Card

/-!
# D14 — published generalized Stone–Wales challenge

This file contains statements only. Each `sorry` is intentional. The `research solved`
metadata refers to the linked public Lean proof; elaborating this file does not check that proof.
The original namespaces, definitions, hypotheses and theorem statements are preserved.

Scope: Positive-domain ray periodicity only. The supporting no-path lemma is not added as a new challenge statement.

*References:*
- A. Bille, V. Buchstaber, E. Spodarev, *Some Open Mathematical Problems on Fullerenes*,
  J. Chem. Inf. Model. 65 (2025), 2911–2923, https://doi.org/10.1021/acs.jcim.4c01997.
  Literal path definition: Definition 1(a) of https://arxiv.org/abs/2410.19322v1.
- T. Takimoto, *Eventual periodicity of linear generalized Stone-Wales paths in affine fullerene families with convex lattice-face decompositions*, paper version 6.2,
  https://doi.org/10.5281/zenodo.23540600.
- Public source challenge (fixed commit):
  https://github.com/tkmt-lab/gsw-ray-periodicity/blob/8a53918db58fa6949ce0f868aa8dcb89be3345d5/statement/ChallengeD14.lean.

The original challenge notes below are retained verbatim; their comments about imports
refer to the original file, before the metadata import in this normalized copy.
-/

@[expose] public section

-- BEGIN ORIGINAL CHALLENGE BODY (metadata attributes are the only insertions below)

/-!
# Challenge statement: D14 path existence is eventually periodic on every ray

Written by Claude (statement writer) on 2026-10-20, before any proof, as a Comparator
"challenge". It contains one `sorry`: the statement to be proved elsewhere. Only Mathlib is
imported.

The definitions are copied verbatim from `ClaudeChallengeSpec.lean` (namespace
`ClaudeChallenge`: `rot`, `rotN`, `unitVec`, `deg`, `LiteralPath`), from `Claude2AlignedSpec.lean`
(namespace `Claude2Aligned`: labelled lattice polygons glued along equally labelled sides) and
from `Claude5D14Spec.lean` (Graver's D14). Only `PathExists` and the theorems are new.

Reading guide:
1. `d14Poly`, `d14Lab` : Graver's D14(r,s). Two hexagons with sides `s, 2r + s`; each long
   side is cut `r, s, r` by two straight-angle corners. Both cells carry the twelve labels
   `0 … 11` (in opposite orders); the side between labels `j, j+1` has length `s` (`j` even) or
   `r` (`j` odd). Parameters: `r, s` are the paper's and R004's (`d14.py`). Twice the area is
   `8r² + 24rs + 12s²`.
2. `InCell`, `Glue`, `SamePoint`, `Vertex`, `graph` : as for K3 and C1.
3. `LiteralPath` : Definition 1(a) of Bille–Buchstaber–Spodarev (same as the first paper).
4. `main` : on every integer ray `(r₀ + a n, s₀ + b n)` with `r₀, s₀ ≥ 1`, `a, b ≥ 0`,
   literal-path existence is eventually periodic (Corollary 1b for D14).
   No classification is stated: the paper has only absence drafts for `r, s ≥ 2` (`prop:partial`),
   not a received closed condition.

Corollary 1b of the second paper quantifies integer affine rays that eventually stay in the
valid positive domain `r, s ≥ 1`. Such a ray has nonnegative slopes, and after shifting its index it
starts in the domain, so it is covered by `main` (natural starts at least `1`, natural slopes;
the parameter-1 boundaries are included). Nothing here assumes `Valid` or `TrianglesInCharts`.
-/

namespace ClaudeChallenge

/-- The 60° rotation of the triangular lattice in the basis (1,0), (0,1)=rot(1,0). -/
def rot (z : ℤ × ℤ) : ℤ × ℤ := (-z.2, z.1 + z.2)

/-- `rot` applied `n` times. -/
def rotN : ℕ → ℤ × ℤ → ℤ × ℤ
  | 0, z => z
  | n + 1, z => rot (rotN n z)

/-- The six unit vectors of the triangular lattice. -/
def unitVec : List (ℤ × ℤ) := [(1, 0), (0, 1), (-1, 1), (-1, 0), (0, -1), (1, -1)]

/-- Degree, as the cardinality of the neighbour set (finite for these graphs). -/
noncomputable def deg {V : Type} (G : SimpleGraph V) (v : V) : ℕ := (G.neighborSet v).ncard

/-- Literal linear gSW path `p 0, …, p (n-1)` (Definition 1(a) of Bille–Buchstaber–Spodarev):
an even number `n ≥ 4` of distinct vertices, consecutive and distance-two members adjacent,
degree-five ends whose neighbours on the path have degree six. -/
def LiteralPath {V : Type} (G : SimpleGraph V) (n : ℕ) (p : ℕ → V) : Prop :=
  4 ≤ n ∧ Even n ∧
    (∀ i j, i < n → j < n → p i = p j → i = j) ∧
    (∀ i, i + 1 < n → G.Adj (p i) (p (i + 1))) ∧
    (∀ i, i + 2 < n → G.Adj (p i) (p (i + 2))) ∧
    deg G (p 0) = 5 ∧ deg G (p (n - 1)) = 5 ∧
    deg G (p 1) = 6 ∧ deg G (p (n - 2)) = 6

end ClaudeChallenge

namespace Claude2Aligned

open ClaudeChallenge

/-- A signature: `N` convex lattice polygons with labelled corners. -/
structure Sig where
  N : ℕ
  lab : Fin N → List ℕ
  poly : Fin N → List (ℤ × ℤ)

/-- Planar cross product. -/
def cross (a b : ℤ × ℤ) : ℤ := a.1 * b.2 - a.2 * b.1

namespace Sig

variable (S : Sig)

/-- Corner `i` (cyclically) of cell `f`. -/
def pt (f : Fin S.N) (i : ℕ) : ℤ × ℤ := (S.poly f).getD (i % (S.poly f).length) 0

/-- Label of corner `i` (cyclically) of cell `f`. -/
def lb (f : Fin S.N) (i : ℕ) : ℕ := (S.lab f).getD (i % (S.lab f).length) 0

/-- `z` lies in the closed polygon of cell `f` (corners listed counterclockwise). -/
def InCell (f : Fin S.N) (z : ℤ × ℤ) : Prop :=
  ∀ i < (S.poly f).length, 0 ≤ cross (S.pt f (i + 1) - S.pt f i) (z - S.pt f i)

/-- Edge `i` of `g` (labels `a → b`) is glued to edge `j` of `f` (labels `b → a`) by
`z ↦ rotN m z + τ`, which carries the corner `a` of `g` to the corner `a` of `f` and likewise
for `b`. -/
def Glue (g : Fin S.N) (i : ℕ) (f : Fin S.N) (j : ℕ) (m : ℕ) (τ : ℤ × ℤ) : Prop :=
  i < (S.poly g).length ∧ j < (S.poly f).length ∧
    S.lb g i = S.lb f (j + 1) ∧ S.lb g (i + 1) = S.lb f j ∧
    rotN m (S.pt g i) + τ = S.pt f (j + 1) ∧ rotN m (S.pt g (i + 1)) + τ = S.pt f j

/-- A site: a cell and a lattice point of its closed polygon. -/
abbrev Site : Type := {p : Fin S.N × (ℤ × ℤ) // S.InCell p.1 p.2}

/-- One step of the identification of boundary points. -/
def SamePoint (s s' : S.Site) : Prop :=
  ∃ i j m τ, S.Glue s.1.1 i s'.1.1 j m τ ∧ rotN m s.1.2 + τ = s'.1.2

/-- Vertices of the triangulated sphere. -/
abbrev Vertex : Type := Quot (Relation.EqvGen S.SamePoint)

/-- The vertex of a site. -/
def vtx (s : S.Site) : S.Vertex := Quot.mk _ s

/-- `s'` is a unit step from `s` inside one cell. -/
def StepTo (s s' : S.Site) : Prop := s'.1.1 = s.1.1 ∧ s'.1.2 - s.1.2 ∈ unitVec

/-- The triangulation (dual of the fullerene). -/
def graph : SimpleGraph S.Vertex where
  Adj v w := v ≠ w ∧ ∃ s s' : S.Site, S.vtx s = v ∧ S.vtx s' = w ∧ (S.StepTo s s' ∨ S.StepTo s' s)
  symm := ⟨fun _ _ ⟨h, s, s', hs, hs', h'⟩ => ⟨fun e => h e.symm, s', s, hs', hs, h'.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

end Sig

/-- Lattice walk: start at `p`, then for each `(len, k)` move by `len` steps in direction
`rotN k (1, 0)`; the list of corners visited before each move. -/
def walk : ℤ × ℤ → List (ℤ × ℕ) → List (ℤ × ℤ)
  | _, [] => []
  | p, (len, k) :: rest => p :: walk (p + rotN k (len, 0)) rest

/-! ## D14(r,s) -/

/-- D14 labels: the two 12-gons share all twelve labels, in opposite orders (as for D12). -/
def d14Lab : Fin 2 → List ℕ :=
  ![[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], [0, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1]]

/-- D14 polygons: the side between labels `j` and `j + 1` has length `s` for even `j` and `r`
for odd `j`. In cell 0 the corners `2, 3, 6, 7, 10, 11` are straight, in cell 1 the corners
`0, 1, 4, 5, 8, 9`; so each cell is a hexagon with sides `s, 2r + s`. -/
def d14Poly (r s : ℤ) (f : Fin 2) : List (ℤ × ℤ) :=
  if f.val = 0 then
    walk (0, 0) [(s, 0), (r, 1), (s, 1), (r, 1), (s, 2), (r, 3),
      (s, 3), (r, 3), (s, 4), (r, 5), (s, 5), (r, 5)]
  else
    walk (0, 0) [(r, 0), (s, 1), (r, 2), (s, 2), (r, 2), (s, 3),
      (r, 4), (s, 4), (r, 4), (s, 5), (r, 0), (s, 0)]

def d14Sig (r s : ℤ) : Sig := ⟨2, d14Lab, d14Poly r s⟩

/-- The dual graph of Graver's D14(r,s). -/
def d14Graph (r s : ℤ) : SimpleGraph (d14Sig r s).Vertex := (d14Sig r s).graph

end Claude2Aligned

namespace ClaudeChallengeD14

open ClaudeChallenge Claude2Aligned

/-- A literal path exists in D14(r,s). -/
def PathExists (r s : ℤ) : Prop := ∃ n p, LiteralPath (d14Graph r s) n p

/-- **D14 on rays**: on every integer ray `(r₀ + a n, s₀ + b n)` with `r₀, s₀ ≥ 1`, `a, b ≥ 0`,
literal-path existence in D14 is eventually periodic. -/
@[category research solved, AMS 5 37 92, formal_proof using lean4 at
  "https://github.com/tkmt-lab/gsw-ray-periodicity/blob/8a53918db58fa6949ce0f868aa8dcb89be3345d5/packet/formal/Formal/Claude5D14ComparatorSolution.lean#L29"]
theorem main (r₀ s₀ a b : ℕ) (hr : 1 ≤ r₀) (hs : 1 ≤ s₀) :
    ∃ n₀ P : ℕ, 0 < P ∧ ∀ n : ℕ, n₀ ≤ n →
      (PathExists (r₀ + a * n) (s₀ + b * n) ↔
        PathExists (r₀ + a * (n + P)) (s₀ + b * (n + P))) := by
  sorry

end ClaudeChallengeD14
