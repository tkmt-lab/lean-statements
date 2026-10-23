/-
Copyright 2026 Tatsuhiko Takimoto.
SPDX-License-Identifier: Apache-2.0
-/
module

public meta import FormalConjecturesUtil.Attributes.Basic

/-!
# Metadata-only facade for the statement copies

The two imported attribute files are copied from formal-conjectures at the commit in manifest.json.
This facade intentionally omits the full upstream project, its extra mathematics, and its linters.
The problem files retain their own original Mathlib imports. Replace this facade with the real
FormalConjecturesUtil when importing an individual statement into formal-conjectures.
-/
