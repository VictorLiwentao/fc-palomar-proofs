/-
Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 Wentao Li.

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

public import Mathlib

/-!
# Challenge: Kolberg's theorem on the parity of the partition function

`Nat.partitionNumber` is copied verbatim from
`FormalConjecturesForMathlib/Combinatorics/Enumerative/Partition/Basic.lean`, and the statement of
`kolberg` from `FormalConjectures/Paper/PartitionParity.lean`, in google-deepmind/formal-conjectures
at commit `691719db2653905d5fa0775408370fb058e4c59f` (The Formal Conjectures Authors,
Apache-2.0). The `sorry` marks the statement to be proved; it is not a proof.
-/

@[expose] public section

namespace Nat

def partitionNumber : ℕ → ℕ := fun n ↦ Fintype.card (Nat.Partition n)

end Nat

namespace PartitionParity

open Nat Real Filter Topology Asymptotics Polynomial

theorem kolberg :
    {n : ℕ | Even (partitionNumber n)}.Infinite ∧ {n : ℕ | Odd (partitionNumber n)}.Infinite := by
  sorry

end PartitionParity

end
