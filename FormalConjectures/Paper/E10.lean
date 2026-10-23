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
public import Mathlib.Data.Int.ModEq

/-!
# E10 — published generalized Stone–Wales challenge

This file contains statements only. Each `sorry` is intentional. The `research solved`
metadata refers to the linked public Lean proof; elaborating this file does not check that proof.
The original namespaces, definitions, hypotheses and theorem statements are preserved.

Scope: Classification for p,s >= 1 and r >= 2; positive-domain ray periodicity includes r = 1. No r = 1 closed classification is asserted.

*References:*
- A. Bille, V. Buchstaber, E. Spodarev, *Some Open Mathematical Problems on Fullerenes*,
  J. Chem. Inf. Model. 65 (2025), 2911–2923, https://doi.org/10.1021/acs.jcim.4c01997.
  Literal path definition: Definition 1(a) of https://arxiv.org/abs/2410.19322v1.
- T. Takimoto, *Eventual periodicity of linear generalized Stone-Wales paths in affine fullerene families with convex lattice-face decompositions*, paper version 6.2,
  https://doi.org/10.5281/zenodo.23540600.
- Public source challenge (fixed commit):
  https://github.com/tkmt-lab/gsw-ray-periodicity/blob/8a53918db58fa6949ce0f868aa8dcb89be3345d5/statement/ChallengeE10.lean.

The original challenge notes below are retained verbatim; their comments about imports
refer to the original file, before the metadata import in this normalized copy.
-/

@[expose] public section

-- BEGIN ORIGINAL CHALLENGE BODY (metadata attributes are the only insertions below)

/-!
# Challenge statement: E10 path existence (classification for `r ≥ 2`, and rays)

Written by Claude (statement writer) on 2026-10-20, before any proof, as a Comparator
"challenge". It contains two `sorry`s: the statements to be proved elsewhere. Only Mathlib is
imported.

The definitions are copied verbatim from `ClaudeChallengeSpec.lean` (namespace
`ClaudeChallenge`: `rot`, `rotN`, `unitVec`, `deg`, `LiteralPath`), from `Claude2AlignedSpec.lean`
(namespace `Claude2Aligned`: labelled lattice polygons glued along equally labelled sides) and
from `Claude5E10Spec.lean` (Graver's E10, aligned retiling). Only `PathExists` and the theorems are new.

Reading guide:
1. `e10Cell`, `e10Lab`, `e10Poly` : Graver's E10(p,r,s) as five convex lattice polygons (the
   paper's `sec:families` retiling: the longitudinal cut moved from `(p,p)` to `(0,2p)`). Cell 0 and
   cell 1 are the two hexagonal caps (sides alternating `r`, `r + s`); cells 2–4 are the three
   tube parallelograms of width `m = 2r + s` and height `2p`. Where the tube cuts meet the upper
   cap away from its corners (`k = p mod m ∉ {0, r}`), auxiliary straight-angle corners
   `12, 13, 14` are inserted; `j = (p div m) mod 3` says which upper-cap corners lie in which
   sector. Parameters: `p, r, s` are the paper's and R004's (`e10_aligned.py`). Twice the area
   is `12r² + 2s² + 12rs + 24pr + 12ps`.
2. `InCell`, `Glue`, `SamePoint`, `Vertex`, `graph` : as for K3 and C1.
3. `LiteralPath` : Definition 1(a) of Bille–Buchstaber–Spodarev (same as the first paper).
4. `classification` : for `p, s ≥ 1`, `r ≥ 2`, with `m = 2r + s`, a literal path exists iff
   `p ≡ d ± 1 (mod m)` for some `d ∈ {0, r, r + s}` (second paper, table `prop:closed`). The paper
   has no closed condition for `r = 1`, so neither does this file.
5. `main` : on every integer ray `(p₀ + a n, r₀ + b n, s₀ + c n)` with `p₀, r₀, s₀ ≥ 1`,
   `a, b, c ≥ 0`, literal-path existence is eventually periodic (Corollary 1b for E10,
   including the boundary `r = 1`).

Corollary 1b of the second paper quantifies integer affine rays that eventually stay in the
valid positive domain `p, r, s ≥ 1`. Such a ray has nonnegative slopes, and after shifting its index it
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

/-! ## E10(p,r,s) -/

/-- The five E10 cells (labels, polygon). Cell 0: lower cap `L0 … L5`, sides
`r, r+s, r, r+s, r, r+s`. Cell 1: upper cap `U0 U5 U4 U3 U2 U1` (`Uᵢ = 6 + i`), sides
`r+s, r, r+s, r, r+s, r`, with the cut corners `12 + (c mod 3)` inserted on its `r`-sides
(`0 < k < r`) or its `(r+s)`-sides (`k > r`). Cells `2 + c` (`c = 0, 1, 2`): tube sector `c`
between positions `cm` and `(c+1)m`; lower corners `L(6-2c mod 6), L(5-2c), L(4-2c)`, then the
upper boundary from position `(c+1)m` down to `cm`, where `U(2i)` lies at offset `k` (`k ≠ 0`)
and `U(2i+1)` at offset `k - r` or `k - r + m`. -/
def e10Cell (p r s : ℤ) (f : Fin 5) : List ℕ × List (ℤ × ℤ) :=
  let m := 2 * r + s
  let k := p % m
  let j := ((p / m) % 3).toNat
  let e : ℕ → ℕ := fun i => 6 + 2 * (i % 3)
  let o : ℕ → ℕ := fun i => 7 + 2 * (i % 3)
  let cut : ℕ → ℕ := fun c => 12 + c % 3
  if f.val = 0 then
    ([0, 1, 2, 3, 4, 5],
      walk (0, 0) [(r, 0), (r + s, 1), (r, 2), (r + s, 3), (r, 4), (r + s, 5)])
  else if f.val = 1 then
    if k = 0 ∨ k = r then
      ([6, 11, 10, 9, 8, 7],
        walk (0, 0) [(r + s, 0), (r, 1), (r + s, 2), (r, 3), (r + s, 4), (r, 5)])
    else if k < r then
      ([6, 11, cut (j + 1), 10, 9, cut (j + 2), 8, 7, cut j],
        walk (0, 0) [(r + s, 0), (r - k, 1), (k, 1), (r + s, 2), (r - k, 3), (k, 3),
          (r + s, 4), (r - k, 5), (k, 5)])
    else
      ([6, cut (j + 1), 11, 10, cut (j + 2), 9, 8, cut j, 7],
        walk (0, 0) [(m - k, 0), (k - r, 0), (r, 1), (m - k, 2), (k - r, 2), (r, 3),
          (m - k, 4), (k - r, 4), (r, 5)])
  else
    let c := f.val - 2
    let a := (j + 3 - c) % 3
    let b := (j + 5 - c) % 3
    let low := [(6 - 2 * c) % 6, 5 - 2 * c, 4 - 2 * c]
    if k = 0 then
      (low ++ [e b, o b, e a],
        walk (0, 0) [(m - r, 5), (r, 5), (2 * p, 1), (r, 2), (m - r, 2), (2 * p, 4)])
    else if k < r then
      (low ++ [cut (c + 1), o b, e a, cut c],
        walk (0, 0) [(m - r, 5), (r, 5), (2 * p, 1), (r - k, 2), (m - r, 2), (k, 2), (2 * p, 4)])
    else if k = r then
      (low ++ [o b, e a, o a],
        walk (0, 0) [(m - r, 5), (r, 5), (2 * p, 1), (m - r, 2), (r, 2), (2 * p, 4)])
    else
      (low ++ [cut (c + 1), e a, o a, cut c],
        walk (0, 0) [(m - r, 5), (r, 5), (2 * p, 1), (m - k, 2), (r, 2), (k - r, 2), (2 * p, 4)])

/-- Corner labels of the E10 cells. -/
def e10Lab (p r s : ℤ) (f : Fin 5) : List ℕ := (e10Cell p r s f).1

/-- E10 cell polygons. -/
def e10Poly (p r s : ℤ) (f : Fin 5) : List (ℤ × ℤ) := (e10Cell p r s f).2

def e10Sig (p r s : ℤ) : Sig := ⟨5, e10Lab p r s, e10Poly p r s⟩

/-- The dual graph of Graver's E10(p,r,s). -/
def e10Graph (p r s : ℤ) : SimpleGraph (e10Sig p r s).Vertex := (e10Sig p r s).graph

end Claude2Aligned

namespace ClaudeChallengeE10

open ClaudeChallenge Claude2Aligned

/-- A literal path exists in E10(p,r,s). -/
def PathExists (p r s : ℤ) : Prop := ∃ n q, LiteralPath (e10Graph p r s) n q

/-- **E10 classification**: for `p, s ≥ 1` and `r ≥ 2`, a literal path exists iff
`p ≡ d + 1` or `p ≡ d - 1 (mod 2r + s)` for some `d ∈ {0, r, r + s}`. -/
@[category research solved, AMS 5 37 92, formal_proof using lean4 at
  "https://github.com/tkmt-lab/gsw-ray-periodicity/blob/8a53918db58fa6949ce0f868aa8dcb89be3345d5/packet/formal/Formal/Claude5E10ComparatorSolution.lean#L31"]
theorem classification (p r s : ℕ) (hp : 1 ≤ p) (hr : 2 ≤ r) (hs : 1 ≤ s) :
    PathExists p r s ↔
      ∃ d : ℤ, (d = 0 ∨ d = r ∨ d = r + s) ∧
        ((p : ℤ) ≡ d + 1 [ZMOD 2 * r + s] ∨ (p : ℤ) ≡ d - 1 [ZMOD 2 * r + s]) := by
  sorry

/-- **E10 on rays**: on every integer ray `(p₀ + a n, r₀ + b n, s₀ + c n)` with
`p₀, r₀, s₀ ≥ 1`, `a, b, c ≥ 0`, literal-path existence in E10 is eventually periodic. -/
@[category research solved, AMS 5 37 92, formal_proof using lean4 at
  "https://github.com/tkmt-lab/gsw-ray-periodicity/blob/8a53918db58fa6949ce0f868aa8dcb89be3345d5/packet/formal/Formal/Claude5E10ComparatorSolution.lean#L40"]
theorem main (p₀ r₀ s₀ a b c : ℕ) (hp : 1 ≤ p₀) (hr : 1 ≤ r₀) (hs : 1 ≤ s₀) :
    ∃ n₀ P : ℕ, 0 < P ∧ ∀ n : ℕ, n₀ ≤ n →
      (PathExists (p₀ + a * n) (r₀ + b * n) (s₀ + c * n) ↔
        PathExists (p₀ + a * (n + P)) (r₀ + b * (n + P)) (s₀ + c * (n + P))) := by
  sorry

end ClaudeChallengeE10
