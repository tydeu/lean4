/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.Option.Basic
import Init.Data.Option.List
import Init.Data.List.Attach
import Init.BinderPredicates

namespace Option

/--
Unsafe implementation of `attachWith`, taking advantage of the fact that the representation of
`Option {x // P x}` is the same as the input `Option α`.
-/
@[inline] private unsafe def attachWithImpl
    (o : Option α) (P : α → Prop) (_ : ∀ x, o = some x → P x) : Option {x // P x} := unsafeCast o

/--
“Attaches” a proof that some predicate holds for an optional value, if present, returning a subtype
that expresses this fact.

This function is primarily used to implement `Option.attach`, which allows definitions by
well-founded recursion that use iteration operators (such as `Option.map`) to prove that an optional
value drawn from a parameter is smaller than the parameter. This allows the well-founded recursion
mechanism to prove that the function terminates.
-/
@[implemented_by attachWithImpl] def attachWith
    (xs : Option α) (P : α → Prop) (H : ∀ x, xs = some x → P x) : Option {x // P x} :=
  match xs with
  | none => none
  | some x => some ⟨x, H x rfl⟩

/--
“Attaches” a proof that an optional value, if present, is indeed this value, returning a subtype
that expresses this fact.

This function is primarily used to allow definitions by well-founded recursion that use iteration
operators (such as `Option.map`) to prove that an optional value drawn from a parameter is smaller
than the parameter. This allows the well-founded recursion mechanism to prove that the function
terminates.
-/
@[inline] def attach (xs : Option α) : Option {x // xs = some x} := xs.attachWith _ fun _ => id

@[simp] theorem attach_none : (none : Option α).attach = none := rfl
@[simp] theorem attachWith_none : (none : Option α).attachWith P H = none := rfl

@[simp] theorem attach_some {x : α} :
    (some x).attach = some ⟨x, rfl⟩ := rfl
@[simp] theorem attachWith_some {x : α} {P : α → Prop} (h : ∀ (b : α), some x = some b → P b) :
    (some x).attachWith P h = some ⟨x, by simpa using h⟩ := rfl

theorem attach_congr {o₁ o₂ : Option α} (h : o₁ = o₂) :
    o₁.attach = o₂.attach.map (fun x => ⟨x.1, h ▸ x.2⟩) := by
  subst h
  simp

theorem attachWith_congr {o₁ o₂ : Option α} (w : o₁ = o₂) {P : α → Prop} {H : ∀ x, o₁ = some x → P x} :
    o₁.attachWith P H = o₂.attachWith P fun _ h => H _ (w ▸ h) := by
  subst w
  simp

theorem attach_map_val (o : Option α) (f : α → β) :
    (o.attach.map fun (i : {i // o = some i}) => f i) = o.map f := by
  cases o <;> simp

@[deprecated attach_map_val (since := "2025-02-17")]
abbrev attach_map_coe := @attach_map_val

theorem attach_map_subtype_val (o : Option α) :
    o.attach.map Subtype.val = o :=
  (attach_map_val _ _).trans (congrFun Option.map_id _)

theorem attachWith_map_val {p : α → Prop} (f : α → β) (o : Option α) (H : ∀ a, o = some a → p a) :
    ((o.attachWith p H).map fun (i : { i // p i}) => f i.val) = o.map f := by
  cases o <;> simp [H]

@[deprecated attachWith_map_val (since := "2025-02-17")]
abbrev attachWith_map_coe := @attachWith_map_val

theorem attachWith_map_subtype_val {p : α → Prop} (o : Option α) (H : ∀ a, o = some a → p a) :
    (o.attachWith p H).map Subtype.val = o :=
  (attachWith_map_val _ _ _).trans (congrFun Option.map_id _)

theorem attach_eq_some : ∀ (o : Option a) (x : {x // o = some x}), o.attach = some x
  | none, ⟨x, h⟩ => by simp at h
  | some a, ⟨x, h⟩ => by simpa using h

theorem mem_attach : ∀ (o : Option α) (x : {x // o = some x}), x ∈ o.attach :=
  attach_eq_some

@[simp] theorem isNone_attach (o : Option α) : o.attach.isNone = o.isNone := by
  cases o <;> simp

@[simp] theorem isNone_attachWith {p : α → Prop} (o : Option α) (H : ∀ a, o = some a → p a) :
    (o.attachWith p H).isNone = o.isNone := by
  cases o <;> simp

@[simp] theorem isSome_attach (o : Option α) : o.attach.isSome = o.isSome := by
  cases o <;> simp

@[simp] theorem isSome_attachWith {p : α → Prop} (o : Option α) (H : ∀ a, o = some a → p a) :
    (o.attachWith p H).isSome = o.isSome := by
  cases o <;> simp

@[simp] theorem attach_eq_none_iff {o : Option α} : o.attach = none ↔ o = none := by
  cases o <;> simp

@[simp] theorem attach_eq_some_iff {o : Option α} {x : {x // o = some x}} :
    o.attach = some x ↔ o = some x.val := by
  cases o <;> cases x <;> simp

@[simp] theorem attachWith_eq_none_iff {p : α → Prop} {o : Option α} (H : ∀ a, o = some a → p a) :
    o.attachWith p H = none ↔ o = none := by
  cases o <;> simp

@[simp] theorem attachWith_eq_some_iff {p : α → Prop} {o : Option α} (H : ∀ a, o = some a → p a) {x : {x // p x}} :
    o.attachWith p H = some x ↔ o = some x.val := by
  cases o <;> cases x <;> simp

@[simp] theorem get_attach {o : Option α} (h : o.attach.isSome = true) :
    o.attach.get h = ⟨o.get (by simpa using h), by simp⟩ := by
  cases o
  · simp at h
  · simp [get_some]

@[simp] theorem get_attachWith {p : α → Prop} {o : Option α} (H : ∀ a, o = some a → p a) (h : (o.attachWith p H).isSome) :
    (o.attachWith p H).get h = ⟨o.get (by simpa using h), H _ (by simp)⟩ := by
  cases o
  · simp at h
  · simp [get_some]

theorem toList_attach (o : Option α) :
    o.attach.toList = o.toList.attach.map fun ⟨x, h⟩ => ⟨x, by simpa using h⟩ := by
  cases o <;> simp

@[simp] theorem attach_toList (o : Option α) :
    o.toList.attach = (o.attach.map fun ⟨a, h⟩ => ⟨a, by simpa using h⟩).toList := by
  cases o <;> simp

theorem attach_map {o : Option α} (f : α → β) :
    (o.map f).attach = o.attach.map (fun ⟨x, h⟩ => ⟨f x, map_eq_some_iff.2 ⟨_, h, rfl⟩⟩) := by
  cases o <;> simp

theorem attachWith_map {o : Option α} (f : α → β) {P : β → Prop} {H : ∀ (b : β), o.map f = some b → P b} :
    (o.map f).attachWith P H = (o.attachWith (P ∘ f) (fun _ h => H _ (map_eq_some_iff.2 ⟨_, h, rfl⟩))).map
      fun ⟨x, h⟩ => ⟨f x, h⟩ := by
  cases o <;> simp

theorem map_attach_eq_pmap {o : Option α} (f : { x // o = some x } → β) :
    o.attach.map f = o.pmap (fun a (h : o = some a) => f ⟨a, h⟩) (fun _ h => h) := by
  cases o <;> simp

@[deprecated map_attach_eq_pmap (since := "2025-02-09")]
abbrev map_attach := @map_attach_eq_pmap

@[simp] theorem map_attachWith {l : Option α} {P : α → Prop} {H : ∀ (a : α), l = some a → P a}
    (f : { x // P x } → β) :
    (l.attachWith P H).map f = l.attach.map fun ⟨x, h⟩ => f ⟨x, H _ h⟩ := by
  cases l <;> simp_all

theorem map_attachWith_eq_pmap {o : Option α} {P : α → Prop} {H : ∀ (a : α), o = some a → P a}
    (f : { x // P x } → β) :
    (o.attachWith P H).map f =
      o.pmap (fun a (h : o = some a ∧ P a) => f ⟨a, h.2⟩) (fun a h => ⟨h, H a h⟩) := by
  cases o <;> simp

@[simp]
theorem map_attach_eq_attachWith {o : Option α} {p : α → Prop} (f : ∀ a, o = some a → p a) :
    o.attach.map (fun x => ⟨x.1, f x.1 x.2⟩) = o.attachWith p f := by
  cases o <;> simp_all [Function.comp_def]

theorem attach_bind {o : Option α} {f : α → Option β} :
    (o.bind f).attach =
      o.attach.bind fun ⟨x, h⟩ => (f x).attach.map fun ⟨y, h'⟩ => ⟨y, bind_eq_some_iff.2 ⟨_, h, h'⟩⟩ := by
  cases o <;> simp

theorem bind_attach {o : Option α} {f : {x // o = some x} → Option β} :
    o.attach.bind f = o.pbind fun a h => f ⟨a, h⟩ := by
  cases o <;> simp

theorem pbind_eq_bind_attach {o : Option α} {f : (a : α) → o = some a → Option β} :
    o.pbind f = o.attach.bind fun ⟨x, h⟩ => f x h := by
  cases o <;> simp

theorem attach_filter {o : Option α} {p : α → Bool} :
    (o.filter p).attach =
      o.attach.bind fun ⟨x, h⟩ => if h' : p x then some ⟨x, by simp_all⟩ else none := by
  cases o with
  | none => simp
  | some a =>
    simp only [filter_some, attach_some]
    ext
    simp only [attach_eq_some_iff, ite_none_right_eq_some, some.injEq, some_bind,
      dite_none_right_eq_some]
    constructor
    · rintro ⟨h, w⟩
      refine ⟨h, by ext; simpa using w⟩
    · rintro ⟨h, rfl⟩
      simp [h]

theorem filter_attach {o : Option α} {p : {x // o = some x} → Bool} :
    o.attach.filter p = o.pbind fun a h => if p ⟨a, h⟩ then some ⟨a, h⟩ else none := by
  cases o <;> simp [filter_some]

/-! ## unattach

`Option.unattach` is the (one-sided) inverse of `Option.attach`. It is a synonym for `Option.map Subtype.val`.

We use it by providing a simp lemma `l.attach.unattach = l`, and simp lemmas which recognize higher order
functions applied to `l : Option { x // p x }` which only depend on the value, not the predicate, and rewrite these
in terms of a simpler function applied to `l.unattach`.

Further, we provide simp lemmas that push `unattach` inwards.
-/

/--
Remove an attached proof that the value in an `Option` is indeed that value.

This function is usually inserted automatically by Lean, rather than explicitly in code. It is
introduced as an intermediate step during the elaboration of definitions by well-founded recursion.

If this function is encountered in a proof state, the right approach is usually the tactic
`simp [Option.unattach, -Option.map_subtype]`.

It is a synonym for `Option.map Subtype.val`.
-/
def unattach {α : Type _} {p : α → Prop} (o : Option { x // p x }) := o.map (·.val)

@[simp] theorem unattach_none {p : α → Prop} : (none : Option { x // p x }).unattach = none := rfl
@[simp] theorem unattach_some {p : α → Prop} {a : { x // p x }} :
  (some a).unattach = a.val := rfl

@[simp] theorem isSome_unattach {p : α → Prop} {o : Option { x // p x }} :
    o.unattach.isSome = o.isSome := by
  simp [unattach]

@[simp] theorem isNone_unattach {p : α → Prop} {o : Option { x // p x }} :
    o.unattach.isNone = o.isNone := by
  simp [unattach]

@[simp] theorem unattach_attach (o : Option α) : o.attach.unattach = o := by
  cases o <;> simp

@[simp] theorem unattach_attachWith {p : α → Prop} {o : Option α}
    {H : ∀ a, o = some a → p a} :
    (o.attachWith p H).unattach = o := by
  cases o <;> simp

/-! ### Recognizing higher order functions on subtypes using a function that only depends on the value. -/

/--
This lemma identifies maps over lists of subtypes, where the function only depends on the value, not the proposition,
and simplifies these to the function directly taking the value.
-/
@[simp] theorem map_subtype {p : α → Prop} {o : Option { x // p x }}
    {f : { x // p x } → β} {g : α → β} (hf : ∀ x h, f ⟨x, h⟩ = g x) :
    o.map f = o.unattach.map g := by
  cases o <;> simp [hf]

@[simp] theorem bind_subtype {p : α → Prop} {o : Option { x // p x }}
    {f : { x // p x } → Option β} {g : α → Option β} (hf : ∀ x h, f ⟨x, h⟩ = g x) :
    (o.bind f) = o.unattach.bind g := by
  cases o <;> simp [hf]

@[simp] theorem unattach_filter {p : α → Prop} {o : Option { x // p x }}
    {f : { x // p x } → Bool} {g : α → Bool} (hf : ∀ x h, f ⟨x, h⟩ = g x) :
    (o.filter f).unattach = o.unattach.filter g := by
  cases o
  · simp
  · simp only [filter_some, hf, unattach_some]
    split <;> simp

end Option
