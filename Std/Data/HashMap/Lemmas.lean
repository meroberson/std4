/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Std.Data.HashMap.Basic
import Std.Data.HashMap.WF
import Std.Util.ProofWanted

namespace Std.HashMap

/--
Any hash map of size zero has no accessible elements.
-/
theorem find?_none_of_size_zero [BEq α] [Hashable α] (m : HashMap α β) :
    m.size = 0 → ∀ (a : α), m.find? a = none := by
  simp[HashMap.size,(Imp.WF.out m.property).left,Imp.Buckets.size,Nat.sum_eq_zero_iff]
  intro h k
  simp[HashMap.find?,HashMap.Imp.find?]
  suffices AssocList.toList _ = [] by rw[this] ; simp
  exact List.length_eq_zero.mp (h _ (by rw[Array.getElem_eq_data_get] ; apply List.get_mem))

/--
A hash map with no accessible elements is size zero under the assumption that every key `a` in `α`
is accessible by some key `b` in `α`, where `a == b` and `hash a = hash b`.
This condition is trivially satisfied when `==` over `α` is reflexive.
-/
theorem size_zero_of_find?_none [BEq α] [Hashable α] (m : HashMap α β)
    (accessibility : ∀ a : α, ∃ b : α, a == b ∧ hash a = hash b) :
    (∀ (a : α), m.find? a = none) → m.size = 0 := by
  simp[HashMap.size,Imp.WF.out m.property,Imp.Buckets.size,Nat.sum_eq_zero_iff]
  intro h a h₀
  cases a with
  | nil => simp
  | cons k v a' =>
    have ⟨k',hk'⟩ := accessibility k
    suffices m.find? k' = some v by simp[h] at this
    simp[List.mem_iff_get] at h₀
    let ⟨i,h₀⟩ := h₀
    have := (Imp.WF.out m.property).right.hash_self i i.isLt
    simp[Array.getElem_eq_data_get] at this
    rw[h₀] at this
    simp[AssocList.All] at this
    simp[HashMap.find?,HashMap.Imp.find?,Imp.mkIdx,this.left,Array.getElem_eq_data_get,←hk'.right]
    rw[h₀]
    simp[List.find?,hk'.left]

/--
The empty hash map `∅` has no accessible elements.
-/
@[simp] theorem empty_find? [BEq α] [Hashable α] {a : α} :
    (∅ : HashMap α β).find? a = none := by
  apply find?_none_of_size_zero ; rfl

/--
Insertion behaves correctly with respect to the `find?` operation when the hash is lawful and
boolean equality is sane.
-/
theorem insert_find? [BEq α] [Hashable α] [PartialEquivBEq α] [LawfulHashable α]
    (m : HashMap α β) (a a' : α) (b : β) :
    (m.insert a b).find? a' = if a' == a then some b else m.find? a' := by
  exact Imp.insert_find? (Imp.WF.out m.property).2
