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
# D12 — published classification and positive-domain ray challenge

This file contains statements only. Each `sorry` is intentional. The `research solved`
metadata refers to the linked public Lean proof; elaborating this file does not check that proof.
The original namespaces, definitions, hypotheses and theorem statements are preserved.

Scope: for r, s ≥ 1, literal-path existence is equivalent to the stated integer
arithmetic condition. Eventual periodicity holds for natural starts r₀, s₀ ≥ 1 and
nonnegative natural slopes, including parameter-one boundaries and constant rays.
The explicit quotient graph and the literal-path definition remain unchanged.

*References:*
- T. Takimoto, *Eventual periodicity of linear generalized Stone–Wales paths in
  affine fullerene families with convex lattice-face decompositions*, paper 6.3,
  verification release v1.10.0. All-version archive: https://doi.org/10.5281/zenodo.23491204.
- Public source challenge (fixed commit):
  https://github.com/tkmt-lab/gsw-ray-periodicity/blob/8eea5994bfebdcca4865528bd7524af4064f9c16/statement/ChallengeD12.lean.

The original challenge notes below are retained verbatim; their comments about imports
refer to the original file, before the metadata import in this normalized copy.
-/

@[expose] public section

-- BEGIN ORIGINAL CHALLENGE BODY (metadata attributes are the only insertions below)

/-!
# Challenge statement: D12 path existence (closed classification, and rays)

Written by Claude (statement writer) on 2026-10-21, before any proof, as a Comparator
"challenge". It contains two `sorry`s: the statements to be proved elsewhere. Only Mathlib is
imported.

The definitions are copied verbatim from `ClaudeChallengeSpec.lean` (namespace
`ClaudeChallenge`: `rot`, `rotN`, `unitVec`, `deg`, `LiteralPath`) and from
`Claude2AlignedSpec.lean` (namespace `Claude2Aligned`: labelled lattice polygons glued along
equally labelled sides, and Graver's D12, which `Claude7D12Spec.lean` re-exports). Only
`PathExists` and the theorems are new.

Reading guide:
1. `d12Poly`, `d12Lab` : Graver's D12(r,s). Two regular hexagons of side `L = r + 2s`; each side
   is cut at a label into `s` and `r + s`, in opposite orders on the two cells. Both cells carry
   the twelve labels `0 … 11` (in opposite orders); equally labelled segments are glued in
   reverse order. Parameters: `r, s` are the paper's (`sec:d12-classification`, `L = r + 2s`)
   and R004's (`d12.py`). Twice the area is `12r² + 48rs + 48s²`.
2. `InCell`, `Glue`, `SamePoint`, `Vertex`, `graph` : as for K3, C1 and D14.
3. `LiteralPath` : Definition 1(a) of Bille–Buchstaber–Spodarev (same as the first paper).
4. `classification` : for `r, s ≥ 1`, a literal path exists iff `r ∣ s - 1` or `r ∣ s + 1` or
   `|r - 3s| = 1` (second paper, `thm:d12-classification`; divisibility and the absolute value
   are taken in `ℤ`).
5. `main` : on every integer ray `(r₀ + a n, s₀ + b n)` with `r₀, s₀ ≥ 1`, `a, b ≥ 0`,
   literal-path existence is eventually periodic (Corollary 1b for D12).

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

/-! ## D12(r,s) -/

/-- D12 labels: the two 12-gons share all twelve labels, in opposite orders. -/
def d12Lab : Fin 2 → List ℕ :=
  ![[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], [0, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1]]

/-- D12 polygons: regular hexagons of side `r + 2s`, each side cut at a label into `s` and
`r + s` (in opposite orders on the two disks). -/
def d12Poly (r s : ℤ) (f : Fin 2) : List (ℤ × ℤ) :=
  if f.val = 0 then
    walk (0, 0) [(s, 0), (r + s, 1), (s, 1), (r + s, 2), (s, 2), (r + s, 3),
      (s, 3), (r + s, 4), (s, 4), (r + s, 5), (s, 5), (r + s, 0)]
  else
    walk (0, 0) [(r + s, 0), (s, 0), (r + s, 1), (s, 1), (r + s, 2), (s, 2),
      (r + s, 3), (s, 3), (r + s, 4), (s, 4), (r + s, 5), (s, 5)]

def d12Sig (r s : ℤ) : Sig := ⟨2, d12Lab, d12Poly r s⟩

/-- The dual graph of Graver's D12(r,s). -/
def d12Graph (r s : ℤ) : SimpleGraph (d12Sig r s).Vertex := (d12Sig r s).graph

end Claude2Aligned

namespace ClaudeChallengeD12

open ClaudeChallenge Claude2Aligned

/-- A literal path exists in D12(r,s). -/
def PathExists (r s : ℤ) : Prop := ∃ n p, LiteralPath (d12Graph r s) n p

/-- **D12 classification**: for `r, s ≥ 1`, a literal path exists iff `r ∣ s - 1` or
`r ∣ s + 1` or `|r - 3s| = 1`. -/
@[category research solved, formal_proof using lean4 at
  "https://github.com/tkmt-lab/gsw-ray-periodicity/blob/8eea5994bfebdcca4865528bd7524af4064f9c16/packet/formal/Formal/Claude7D12ComparatorSolution.lean#L32"]
theorem classification (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    PathExists r s ↔
      ((r : ℤ) ∣ (s : ℤ) - 1 ∨ (r : ℤ) ∣ (s : ℤ) + 1 ∨ |(r : ℤ) - 3 * (s : ℤ)| = 1) := by
  sorry

/-- **D12 on rays**: on every integer ray `(r₀ + a n, s₀ + b n)` with `r₀, s₀ ≥ 1`, `a, b ≥ 0`,
literal-path existence in D12 is eventually periodic. -/
@[category research solved, formal_proof using lean4 at
  "https://github.com/tkmt-lab/gsw-ray-periodicity/blob/8eea5994bfebdcca4865528bd7524af4064f9c16/packet/formal/Formal/Claude7D12ComparatorSolution.lean#L39"]
theorem main (r₀ s₀ a b : ℕ) (hr : 1 ≤ r₀) (hs : 1 ≤ s₀) :
    ∃ n₀ P : ℕ, 0 < P ∧ ∀ n : ℕ, n₀ ≤ n →
      (PathExists (r₀ + a * n) (s₀ + b * n) ↔
        PathExists (r₀ + a * (n + P)) (s₀ + b * (n + P))) := by
  sorry

end ClaudeChallengeD12
