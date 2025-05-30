/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kim Morrison
-/
prelude
import Init.Data.List.Basic
import Init.Data.Fin.Fold

/-!
# Theorems about `List.ofFn`
-/

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace List

/--
Creates a list by applying `f` to each potential index in order, starting at `0`.

Examples:
 * `List.ofFn (n := 3) toString = ["0", "1", "2"]`
 * `List.ofFn (fun i => #["red", "green", "blue"].get i.val i.isLt) = ["red", "green", "blue"]`
-/
def ofFn {n} (f : Fin n → α) : List α := Fin.foldr n (f · :: ·) []

@[simp]
theorem length_ofFn {f : Fin n → α} : (ofFn f).length = n := by
  simp only [ofFn]
  induction n with
  | zero => simp
  | succ n ih => simp [Fin.foldr_succ, ih]

@[simp]
protected theorem getElem_ofFn {f : Fin n → α} (h : i < (ofFn f).length) :
    (ofFn f)[i] = f ⟨i, by simp_all⟩ := by
  simp only [ofFn]
  induction n generalizing i with
  | zero => simp at h
  | succ n ih =>
    match i with
    | 0 => simp [Fin.foldr_succ]
    | i+1 =>
      simp only [Fin.foldr_succ]
      apply ih
      simp_all

@[simp]
protected theorem getElem?_ofFn {f : Fin n → α} : (ofFn f)[i]? = if h : i < n then some (f ⟨i, h⟩) else none :=
  if h : i < (ofFn f).length
  then by
    rw [getElem?_eq_getElem h, List.getElem_ofFn]
    · simp only [length_ofFn] at h; simp [h]
  else by
    rw [dif_neg] <;>
    simpa using h

/-- `ofFn` on an empty domain is the empty list. -/
@[simp]
theorem ofFn_zero {f : Fin 0 → α} : ofFn f = [] :=
  ext_get (by simp) (fun i hi₁ hi₂ => by contradiction)

@[simp]
theorem ofFn_succ {n} {f : Fin (n + 1) → α} : ofFn f = f 0 :: ofFn fun i => f i.succ :=
  ext_get (by simp) (fun i hi₁ hi₂ => by
    cases i
    · simp
    · simp)

@[simp]
theorem ofFn_eq_nil_iff {f : Fin n → α} : ofFn f = [] ↔ n = 0 := by
  cases n <;> simp only [ofFn_zero, ofFn_succ, eq_self_iff_true, Nat.succ_ne_zero, reduceCtorEq]

@[simp 500]
theorem mem_ofFn {n} {f : Fin n → α} {a : α} : a ∈ ofFn f ↔ ∃ i, f i = a := by
  constructor
  · intro w
    obtain ⟨i, h, rfl⟩ := getElem_of_mem w
    exact ⟨⟨i, by simpa using h⟩, by simp⟩
  · rintro ⟨i, rfl⟩
    apply mem_of_getElem (i := i) <;> simp

theorem head_ofFn {n} {f : Fin n → α} (h : ofFn f ≠ []) :
    (ofFn f).head h = f ⟨0, Nat.pos_of_ne_zero (mt ofFn_eq_nil_iff.2 h)⟩ := by
  rw [← getElem_zero (length_ofFn ▸ Nat.pos_of_ne_zero (mt ofFn_eq_nil_iff.2 h)),
    List.getElem_ofFn]

theorem getLast_ofFn {n} {f : Fin n → α} (h : ofFn f ≠ []) :
    (ofFn f).getLast h = f ⟨n - 1, Nat.sub_one_lt (mt ofFn_eq_nil_iff.2 h)⟩ := by
  simp [getLast_eq_getElem, length_ofFn, List.getElem_ofFn]

end List
