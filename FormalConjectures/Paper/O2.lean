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
# O2 — published generalized Stone–Wales challenge

This file contains statements only. Each `sorry` is intentional. The `research solved`
metadata refers to the linked public Lean proof; elaborating this file does not check that proof.
The original namespaces, definitions, hypotheses and theorem statements are preserved.

Scope: Absence for t,d >= 2; periodicity for rays starting in t,d >= 1. No extra existence cases are asserted.

*References:*
- A. Bille, V. Buchstaber, E. Spodarev, *Some Open Mathematical Problems on Fullerenes*,
  J. Chem. Inf. Model. 65 (2025), 2911–2923, https://doi.org/10.1021/acs.jcim.4c01997.
  Literal path definition: Definition 1(a) of https://arxiv.org/abs/2410.19322v1.
- T. Takimoto, *Eventual periodicity of linear generalized Stone-Wales paths in affine fullerene families with convex lattice-face decompositions*, paper version 6.2,
  https://doi.org/10.5281/zenodo.23540600.
- Public source challenge (fixed commit):
  https://github.com/tkmt-lab/gsw-ray-periodicity/blob/8a53918db58fa6949ce0f868aa8dcb89be3345d5/statement/ChallengeO2.lean.

The original challenge notes below are retained verbatim; their comments about imports
refer to the original file, before the metadata import in this normalized copy.
-/

@[expose] public section

-- BEGIN ORIGINAL CHALLENGE BODY (metadata attributes are the only insertions below)

/-!
# Challenge statement: O2 path existence (absence for `t, d ≥ 2`, and rays)

Written by Claude (statement writer) on 2026-10-20, before any proof, as a Comparator
"challenge". It contains two `sorry`s: the statements to be proved elsewhere. Only Mathlib is
imported.

The definitions are copied verbatim from `ClaudeChallengeSpec.lean` (namespace
`ClaudeChallenge`: `rot`, `rotN`, `unitVec`, `deg`, `LiteralPath`), from `Claude2AlignedSpec.lean`
(namespace `Claude2Aligned`: labelled lattice polygons glued along equally labelled sides) and
from `Claude5O2Spec.lean` (Graver's O2). Only `PathExists` and the theorems are new.

Reading guide:
1. `o2Poly`, `o2Lab` : Graver's O2(t,d). Two hexagons with sides `2t, d, 2t, d, 2t, d` (cells 0
   and 1; each `2t`-side has a straight-angle corner at its midpoint) and six triangles of side
   `t` (cells 2–7, three rhombi). Labels `4i, 4i+1, 4i+2, 4i+3` name the signature corners
   `Aᵢ, Bᵢ, Cᵢ, Dᵢ`; sides with the same two labels are glued. Parameters: `t, d` are the
   paper's; R004's `o2.py` calls them `r, s`. Twice the area is `14t² + 16td + 2d²`.
2. `InCell`, `Glue`, `SamePoint`, `Vertex`, `graph` : as for K3 and C1.
3. `LiteralPath` : Definition 1(a) of Bille–Buchstaber–Spodarev (same as the first paper).
4. `classification` : for `t, d ≥ 2` there is no literal path (second paper, `prop:partial`:
   "O2 is received as absent ... for `t, d ≥ 2`"). The paper states nothing for `t = 1` or
   `d = 1`, so neither does this file.
5. `main` : on every integer ray `(t₀ + a n, d₀ + b n)` with `t₀, d₀ ≥ 1`, `a, b ≥ 0`,
   literal-path existence is eventually periodic (Corollary 1b for O2).

Corollary 1b of the second paper quantifies integer affine rays that eventually stay in the
valid positive domain `t, d ≥ 1`. Such a ray has nonnegative slopes, and after shifting its index it
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

/-! ## O2(t,d) -/

/-- Corner labels of the eight O2 cells (`Aᵢ = 4i`, `Bᵢ = 4i + 1`, `Cᵢ = 4i + 2`, `Dᵢ = 4i + 3`):
cell 0 is `A0 B0 C0 A1 B1 C1 A2 B2 C2`, cell 1 is `C2 D2 A2 C1 D1 A1 C0 D0 A0`, and cells
`2 + 2i`, `3 + 2i` are the triangles `Cᵢ Bᵢ Dᵢ` and `Bᵢ Aᵢ Dᵢ`. -/
def o2Lab : Fin 8 → List ℕ :=
  ![[0, 1, 2, 4, 5, 6, 8, 9, 10], [10, 11, 8, 6, 7, 4, 2, 3, 0],
    [2, 1, 3], [1, 0, 3], [6, 5, 7], [5, 4, 7], [10, 9, 11], [9, 8, 11]]

/-- O2 cell polygons: cells 0 and 1 are the hexagon with sides `2t, d, 2t, d, 2t, d`, each
`2t`-side carrying a straight-angle corner at its midpoint (`Bᵢ` resp. `Dᵢ`); cells 2–7 are
triangles of side `t`. -/
def o2Poly (t d : ℤ) (f : Fin 8) : List (ℤ × ℤ) :=
  if f.val < 2 then
    walk (0, 0) [(t, 0), (t, 0), (d, 1), (t, 2), (t, 2), (d, 3), (t, 4), (t, 4), (d, 5)]
  else walk (0, 0) [(t, 0), (t, 2), (t, 4)]

def o2Sig (t d : ℤ) : Sig := ⟨8, o2Lab, o2Poly t d⟩

/-- The dual graph of Graver's O2(t,d). -/
def o2Graph (t d : ℤ) : SimpleGraph (o2Sig t d).Vertex := (o2Sig t d).graph

end Claude2Aligned

namespace ClaudeChallengeO2

open ClaudeChallenge Claude2Aligned

/-- A literal path exists in O2(t,d). -/
def PathExists (t d : ℤ) : Prop := ∃ n p, LiteralPath (o2Graph t d) n p

/-- **O2 absence**: for `t, d ≥ 2`, O2(t,d) has no literal path. -/
@[category research solved, AMS 5 37 92, formal_proof using lean4 at
  "https://github.com/tkmt-lab/gsw-ray-periodicity/blob/8a53918db58fa6949ce0f868aa8dcb89be3345d5/packet/formal/Formal/Claude5O2ComparatorSolution.lean#L27"]
theorem classification (t d : ℕ) (ht : 2 ≤ t) (hd : 2 ≤ d) : ¬ PathExists t d := by
  sorry

/-- **O2 on rays**: on every integer ray `(t₀ + a n, d₀ + b n)` with `t₀, d₀ ≥ 1`, `a, b ≥ 0`,
literal-path existence in O2 is eventually periodic. -/
@[category research solved, AMS 5 37 92, formal_proof using lean4 at
  "https://github.com/tkmt-lab/gsw-ray-periodicity/blob/8a53918db58fa6949ce0f868aa8dcb89be3345d5/packet/formal/Formal/Claude5O2ComparatorSolution.lean#L32"]
theorem main (t₀ d₀ a b : ℕ) (ht : 1 ≤ t₀) (hd : 1 ≤ d₀) :
    ∃ n₀ P : ℕ, 0 < P ∧ ∀ n : ℕ, n₀ ≤ n →
      (PathExists (t₀ + a * n) (d₀ + b * n) ↔
        PathExists (t₀ + a * (n + P)) (d₀ + b * (n + P))) := by
  sorry

end ClaudeChallengeO2
