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
# C1 — published generalized Stone–Wales challenge

This file contains statements only. Each `sorry` is intentional. The `research solved`
metadata refers to the linked public Lean proof; elaborating this file does not check that proof.
The original namespaces, definitions, hypotheses and theorem statements are preserved.

Scope: Classification for r,s >= 1 and positive-domain rays; the IPR clause is outside this statement.

*References:*
- A. Bille, V. Buchstaber, E. Spodarev, *Some Open Mathematical Problems on Fullerenes*,
  J. Chem. Inf. Model. 65 (2025), 2911–2923, https://doi.org/10.1021/acs.jcim.4c01997.
  Literal path definition: Definition 1(a) of https://arxiv.org/abs/2410.19322v1.
- T. Takimoto, *Eventual periodicity of linear generalized Stone-Wales paths in affine fullerene families with convex lattice-face decompositions*, paper version 6.2,
  https://doi.org/10.5281/zenodo.23540600.
- Public source challenge (fixed commit):
  https://github.com/tkmt-lab/gsw-ray-periodicity/blob/8a53918db58fa6949ce0f868aa8dcb89be3345d5/statement/ChallengeC1.lean.

The original challenge notes below are retained verbatim; their comments about imports
refer to the original file, before the metadata import in this normalized copy.
-/

@[expose] public section

-- BEGIN ORIGINAL CHALLENGE BODY (metadata attributes are the only insertions below)

/-!
# Challenge statement: C1 path existence (classification and rays)

Written by Claude (coordinator) on 2026-10-20, before any proof, as a Comparator "challenge".
It contains two `sorry`s: the statements to be proved elsewhere. Only Mathlib is imported.

The definitions are copied verbatim from `ClaudeChallengeSpec.lean` (namespace
`ClaudeChallenge`: `rot`, `rotN`, `unitVec`, `deg`, `LiteralPath`), from `Claude2AlignedSpec.lean`
(namespace `Claude2Aligned`: labelled lattice polygons glued along equally labelled sides) and
from `Claude4C1Spec.lean` (Graver's C1).

Reading guide:
1. `c1Poly`, `c1Lab` : Graver's C1(r,s), the truncated tetrahedron. Four hexagons with sides
   `s, r, s, r, s, r` (one per tetrahedron face) and four triangles of side `r` (one per vertex).
   Label `4a + b` names the corner at tetrahedron vertex `a` pointing towards vertex `b`; sides
   with the same two labels are glued.
2. `InCell`, `Glue`, `SamePoint`, `Vertex`, `graph` : as for K3 (first paper style).
3. `LiteralPath` : Definition 1(a) of Bille–Buchstaber–Spodarev (same as the first paper).
4. `classification` : for `r, s ≥ 1`, a literal path exists iff `s = 1` (second paper, closed
   condition for C1, written there with parameters `a, b`; `s` is the paper's `b`).
5. `main` : on every integer ray `(r₀ + a t, s₀ + b t)` with `r₀, s₀ ≥ 1`, `a, b ≥ 0`,
   literal-path existence is eventually periodic (Corollary 1b for C1).
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

/-! ## C1(r,s) -/

/-- Corner labels of the eight C1 cells: cells `0..3` are the hexagons (tetrahedron faces),
cells `4..7` the triangles (tetrahedron vertices). Label `4a + b`: vertex `a`, towards `b`. -/
def c1Lab : Fin 8 → List ℕ :=
  ![[2, 8, 9, 6, 4, 1], [1, 4, 7, 13, 12, 3], [3, 12, 14, 11, 8, 2], [6, 9, 11, 14, 13, 7],
    [1, 3, 2], [4, 6, 7], [8, 11, 9], [12, 13, 14]]

/-- C1 cell polygons: hexagons with sides `s, r, s, r, s, r` and triangles of side `r`. -/
def c1Poly (r s : ℤ) (f : Fin 8) : List (ℤ × ℤ) :=
  if f.val < 4 then walk (0, 0) [(s, 0), (r, 1), (s, 2), (r, 3), (s, 4), (r, 5)]
  else walk (0, 0) [(r, 0), (r, 2), (r, 4)]

def c1Sig (r s : ℤ) : Sig := ⟨8, c1Lab, c1Poly r s⟩

/-- The dual graph of Graver's C1(r,s). -/
def c1Graph (r s : ℤ) : SimpleGraph (c1Sig r s).Vertex := (c1Sig r s).graph

end Claude2Aligned

namespace ClaudeChallengeC1

open ClaudeChallenge Claude2Aligned

/-- A literal path exists in C1(r,s). -/
def PathExists (r s : ℤ) : Prop := ∃ n p, LiteralPath (c1Graph r s) n p

/-- **C1 classification**: for `r, s ≥ 1`, a literal path exists iff `s = 1`. -/
@[category research solved, AMS 5 37 92, formal_proof using lean4 at
  "https://github.com/tkmt-lab/gsw-ray-periodicity/blob/8a53918db58fa6949ce0f868aa8dcb89be3345d5/packet/formal/Formal/Claude4C1ComparatorSolution.lean#L24"]
theorem classification (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) : PathExists r s ↔ s = 1 := by
  sorry

/-- **C1 on rays**: on every integer ray `(r₀ + a t, s₀ + b t)` with `r₀, s₀ ≥ 1`, `a, b ≥ 0`,
literal-path existence in C1 is eventually periodic. -/
@[category research solved, AMS 5 37 92, formal_proof using lean4 at
  "https://github.com/tkmt-lab/gsw-ray-periodicity/blob/8a53918db58fa6949ce0f868aa8dcb89be3345d5/packet/formal/Formal/Claude4C1ComparatorSolution.lean#L29"]
theorem main (r₀ s₀ a b : ℕ) (hr : 1 ≤ r₀) (hs : 1 ≤ s₀) :
    ∃ t₀ P : ℕ, 0 < P ∧ ∀ t : ℕ, t₀ ≤ t →
      (PathExists (r₀ + a * t) (s₀ + b * t) ↔
        PathExists (r₀ + a * (t + P)) (s₀ + b * (t + P))) := by
  sorry

end ClaudeChallengeC1
