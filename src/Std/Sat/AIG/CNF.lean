/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Std.Sat.CNF
import Std.Sat.AIG.Basic
import Std.Sat.AIG.Lemmas


/-!
This module contains an implementation of a verified Tseitin transformation on AIGs. The key results
are the `toCNF` function and the `toCNF_equisat` correctness statement. The implementation is
done in the style of section 3.4 of the AIGNET paper.
-/

namespace Std
namespace Sat

namespace AIG

namespace Decl

/--
Produce a Tseitin style CNF for a `Decl.const`, using `output` as the tree node variable.
-/
def constToCNF (output : α) (const : Bool) : CNF α :=
  [[(output, const)]]

/--
Produce a Tseitin style CNF for a `Decl.atom`, using `output` as the tree node variable.
-/
def atomToCNF (output : α) (atom : α) : CNF α :=
  [[(output, true), (atom, false)], [(output, false), (atom, true)]]

/--
Produce a Tseitin style CNF for a `Decl.gate`, using `output` as the tree node variable.
-/
def gateToCNF (output : α) (lhs rhs : α) (linv rinv : Bool) : CNF α :=
    -- a ↔ (b and c) as CNF: (¬a ∨ b) ∧ (¬a ∨ c) ∧ (a ∨ ¬b ∨ ¬c)
    -- a ↔ (b and ¬c) as CNF: (¬a ∨ b) ∧ (¬a ∨ ¬c) ∧ (a ∨ ¬b ∨ c)
    -- a ↔ (¬b and c) as CNF: (¬a ∨ ¬b) ∧ (¬a ∨ c) ∧ (a ∨ b ∨ ¬c)
    -- a ↔ (¬b and ¬c) as CNF: (¬a ∨ ¬b) ∧ (¬a ∨ ¬c) ∧ (a ∨ b ∨ c)
   [
     [(output, false), (lhs, !linv)],
     [(output, false), (rhs, !rinv)],
     [(output, true),  (lhs, linv), (rhs, rinv)]
   ]

@[simp]
theorem constToCNF_eval :
    (constToCNF output b).eval assign
      =
    (assign output == b) := by
  simp [constToCNF, CNF.eval, CNF.Clause.eval]

@[simp]
theorem atomToCNF_eval :
    (atomToCNF output a).eval assign
      =
    (assign output == assign a) := by
  simp only [atomToCNF, CNF.eval_cons, CNF.Clause.eval_cons, beq_true, beq_false,
    CNF.Clause.eval_nil, Bool.or_false, CNF.eval_nil, Bool.and_true]
  cases assign output <;> cases assign a <;> decide

@[simp]
theorem gateToCNF_eval :
    (gateToCNF output lhs rhs linv rinv).eval assign
      =
    (assign output == ((Bool.xor (assign lhs) linv) && (Bool.xor (assign rhs) rinv))) := by
  simp only [CNF.eval, gateToCNF, CNF.Clause.eval, List.all_cons, List.any_cons, beq_false,
    List.any_nil, Bool.or_false, beq_true, List.all_nil, Bool.and_true]
  cases assign output
    <;> cases assign lhs
      <;> cases assign rhs
        <;> cases linv
          <;> cases rinv
            <;> decide

end Decl

abbrev CNFVar (aig : AIG Nat) := Nat ⊕ (Fin aig.decls.size)

namespace toCNF

/--
Mix:
1. An assignment for AIG atoms
2. An assignment for auxiliary Tseitin variables
into an assignment that can be used by a CNF produced by our Tseitin transformation.
-/
def mixAssigns {aig : AIG Nat} (assign1 : Nat → Bool) (assign2 : Fin aig.decls.size → Bool) :
    CNFVar aig → Bool
  | .inl var => assign1 var
  | .inr var => assign2 var

/--
Project the atom assignment out of a CNF assignment
-/
def projectLeftAssign (assign : CNFVar aig → Bool) : Nat → Bool := (assign <| .inl ·)

/--
Project the auxiliary variable assignment out of a CNF assignment
-/
def projectRightAssign (assign : CNFVar aig → Bool) : (idx : Nat) → (idx < aig.decls.size) → Bool :=
  fun idx h => assign (.inr ⟨idx, h⟩)

@[simp]
theorem projectLeftAssign_property : (projectLeftAssign assign) x = (assign <| .inl x) := by
  simp [projectLeftAssign]

@[simp]
theorem projectRightAssign_property :
    (projectRightAssign assign) x hx = (assign <| .inr ⟨x, hx⟩) := by
  simp [projectRightAssign]

/--
Given an atom assignment, produce an assignment that will always satisfy the CNF generated by our
Tseitin transformation. This is done by combining the atom assignment with an assignment for the
auxiliary variables, that just evaluates the AIG at the corresponding node.
-/
def cnfSatAssignment (aig : AIG Nat) (assign1 : Nat → Bool) : CNFVar aig → Bool :=
  mixAssigns assign1 (fun idx => ⟦aig, ⟨idx.val, idx.isLt⟩, assign1⟧)

@[simp]
theorem satAssignment_inl : (cnfSatAssignment aig assign1) (.inl x) = assign1 x := by
  simp [cnfSatAssignment, mixAssigns]

@[simp]
theorem satAssignment_inr :
    (cnfSatAssignment aig assign1) (.inr x) = ⟦aig, ⟨x.val, x.isLt⟩, assign1⟧ := by
  simp [cnfSatAssignment, mixAssigns]

/--
The central invariants for the `Cache`.
-/
structure Cache.Inv (cnf : CNF (CNFVar aig)) (marks : Array Bool) (hmarks : marks.size = aig.decls.size) : Prop where
  /--
  If there exists an AIG node that is marked, its children are also guaranteed to be marked already.
  This allows us to conclude that if a gate node is marked, all of its (transitive) children are
  also marked.
  -/
  hmark : ∀ (lhs rhs : Nat) (linv rinv : Bool) (idx : Nat) (hbound : idx < aig.decls.size)
            (_hmarked : marks[idx] = true) (heq : aig.decls[idx] = .gate lhs rhs linv rinv),
              marks[lhs]'(by have := aig.invariant hbound heq; omega) = true
                ∧
              marks[rhs]'(by have := aig.invariant hbound heq; omega) = true
  /--
  Relate satisfiability results about our produced CNF to satisfiability results about the AIG that
  we are processing. The intuition for this is: if a node is marked, its CNF (and all required
  children CNFs according to `hmark`) are already part of the current CNF. Thus the current CNF is
  already mirroring the semantics of the marked node. This means that if the CNF is satisfiable at
  some assignment, we can evaluate the marked node under the atom part of that assignment and will
  get the value that was assigned to the corresponding auxiliary variable as a result.
  -/
  heval : ∀ (assign : CNFVar aig → Bool) (_heval : cnf.eval assign = true) (idx : Nat)
            (hbound : idx < aig.decls.size) (_hmark : marks[idx]'(by omega) = true),
              ⟦aig, ⟨idx, hbound⟩, projectLeftAssign assign⟧ = (projectRightAssign assign) idx hbound


/--
The `Cache` invariant always holds for an empty CNF when all nodes are unmarked.
-/
theorem Cache.Inv_init : Inv ([] : CNF (CNFVar aig)) (mkArray aig.decls.size false) (by simp) where
  hmark := by
    intro lhs rhs linv rinv idx hbound hmarked heq
    simp at hmarked
  heval := by
    intro assign _ idx hbound hmark
    simp at hmark

/--
The CNF cache. It keeps track of AIG nodes that we already turned into CNF to avoid adding the same
CNF twice.
-/
structure Cache (aig : AIG Nat) (cnf : CNF (CNFVar aig)) where
  /--
  Keeps track of AIG nodes that we already turned into CNF.
  -/
  marks : Array Bool
  /--
  There are always as many marks as AIG nodes.
  -/
  hmarks : marks.size = aig.decls.size
  /--
  The invariant to make sure that `marks` is well formed with respect to the `cnf`
  -/
  inv : Cache.Inv cnf marks hmarks

/--
We say that a cache extends another by an index when it doesn't invalidate any entry and has an
entry for that index.
-/
structure Cache.IsExtensionBy (cache1 : Cache aig cnf1) (cache2 : Cache aig cnf2) (new : Nat)
    (hnew : new < aig.decls.size) : Prop where
  /--
  No entry is invalidated.
  -/
  extension : ∀ (idx : Nat) (hidx : idx < aig.decls.size),
                cache1.marks[idx]'(by have := cache1.hmarks; omega) = true
                  →
                cache2.marks[idx]'(by have := cache2.hmarks; omega) = true
  /--
  The second cache is true at the new index.
  -/
  trueAt : cache2.marks[new]'(by have := cache2.hmarks; omega) = true

theorem Cache.IsExtensionBy_trans_left (cache1 : Cache aig cnf1) (cache2 : Cache aig cnf2)
    (cache3 : Cache aig cnf3) (h12 : IsExtensionBy cache1 cache2 new1 hnew1)
    (h23 : IsExtensionBy cache2 cache3 new2 hnew2) : IsExtensionBy cache1 cache3 new1 hnew1 := by
  apply IsExtensionBy.mk
  · intro idx hidx hmarked
    apply h23.extension
    · apply h12.extension
      · exact hmarked
      · omega
    · omega
  · apply h23.extension
    · exact h12.trueAt
    · omega

theorem Cache.IsExtensionBy_trans_right (cache1 : Cache aig cnf1) (cache2 : Cache aig cnf2)
    (cache3 : Cache aig cnf3) (h12 : IsExtensionBy cache1 cache2 new1 hnew1)
    (h23 : IsExtensionBy cache2 cache3 new2 hnew2) : IsExtensionBy cache1 cache3 new2 hnew2 := by
  apply IsExtensionBy.mk
  · intro idx hidx hmarked
    apply h23.extension
    · apply h12.extension
      · exact hmarked
      · omega
    · omega
  · exact h23.trueAt

/--
Cache extension is a reflexive relation.
-/
theorem Cache.IsExtensionBy_rfl (cache : Cache aig cnf) {h} (hmarked : cache.marks[idx]'h = true) :
    Cache.IsExtensionBy cache cache idx (have := cache.hmarks; omega) := by
  apply IsExtensionBy.mk
  · intros
    assumption
  · exact hmarked

theorem Cache.IsExtensionBy_set (cache1 : Cache aig cnf1) (cache2 : Cache aig cnf2) (idx : Nat)
    (hbound : idx < cache1.marks.size) (h : cache2.marks = cache1.marks.set ⟨idx, hbound⟩ true) :
    IsExtensionBy cache1 cache2 idx (by have := cache1.hmarks; omega) := by
  apply IsExtensionBy.mk
  · intro idx hidx hmark
    simp [Array.getElem_set, hmark, h]
  · simp [h]

/--
A cache with no entries is valid for an empty CNF.
-/
def Cache.init (aig : AIG Nat) : Cache aig [] where
  marks := mkArray aig.decls.size false
  hmarks := by simp
  inv := Inv_init

/--
Add a `Decl.const` to a `Cache`.
-/
def Cache.addConst (cache : Cache aig cnf) (idx : Nat) (h : idx < aig.decls.size)
    (htip : aig.decls[idx]'h = .const b) :
    {
      out : Cache aig (Decl.constToCNF (.inr ⟨idx, h⟩) b ++ cnf)
        //
      Cache.IsExtensionBy cache out idx h
    } :=
  have hmarkbound : idx < cache.marks.size := by have := cache.hmarks; omega
  let out :=
    { cache with
      marks := cache.marks.set ⟨idx, hmarkbound⟩ true
      hmarks := by simp [cache.hmarks]
      inv := by
        constructor
        · intro lhs rhs linv rinv idx hbound hmarked heq
          rw [Array.getElem_set] at hmarked
          split at hmarked
          · simp_all
          · have := cache.inv.hmark lhs rhs linv rinv idx hbound hmarked heq
            simp [Array.getElem_set, this]
        · intro assign heval idx hbound hmarked
          rw [Array.getElem_set] at hmarked
          split at hmarked
          · next heq =>
            dsimp only at heq
            simp only [heq, CNF.eval_append, Decl.constToCNF_eval, Bool.and_eq_true, beq_iff_eq]
              at htip heval
            simp only [denote_idx_const htip, projectRightAssign_property, heval]
          · next heq =>
            simp only [CNF.eval_append, Decl.constToCNF_eval, Bool.and_eq_true, beq_iff_eq] at heval
            have := cache.inv.heval assign heval.right idx hbound hmarked
            rw [this]
    }
  ⟨out, IsExtensionBy_set cache out idx hmarkbound (by simp [out])⟩

/--
Add a `Decl.atom` to a cache.
-/
def Cache.addAtom (cache : Cache aig cnf) (idx : Nat) (h : idx < aig.decls.size)
    (htip : aig.decls[idx]'h = .atom a) :
    {
      out : Cache aig ((Decl.atomToCNF (.inr ⟨idx, h⟩) (.inl a)) ++ cnf)
        //
      Cache.IsExtensionBy cache out idx h
    } :=
  have hmarkbound : idx < cache.marks.size := by have := cache.hmarks; omega
  let out :=
    { cache with
      marks := cache.marks.set ⟨idx, hmarkbound⟩ true
      hmarks := by simp [cache.hmarks]
      inv := by
        constructor
        · intro lhs rhs linv rinv idx hbound hmarked heq
          rw [Array.getElem_set] at hmarked
          split at hmarked
          · simp_all
          · have := cache.inv.hmark lhs rhs linv rinv idx hbound hmarked heq
            simp [Array.getElem_set, this]
        · intro assign heval idx hbound hmarked
          rw [Array.getElem_set] at hmarked
          split at hmarked
          · next heq =>
            dsimp only at heq
            simp only [heq, CNF.eval_append, Decl.atomToCNF_eval, Bool.and_eq_true, beq_iff_eq] at htip heval
            simp [heval, denote_idx_atom htip]
          · next heq =>
            simp only [CNF.eval_append, Decl.atomToCNF_eval, Bool.and_eq_true, beq_iff_eq] at heval
            have := cache.inv.heval assign heval.right idx hbound hmarked
            rw [this]
    }
  ⟨out, IsExtensionBy_set cache out idx hmarkbound (by simp [out])⟩

/--
Add a `Decl.gate` to a cache.
-/
def Cache.addGate (cache : Cache aig cnf) {hlb} {hrb} (idx : Nat) (h : idx < aig.decls.size)
    (htip : aig.decls[idx]'h = .gate lhs rhs linv rinv) (hl : cache.marks[lhs]'hlb = true)
    (hr : cache.marks[rhs]'hrb = true) :
    {
      out : Cache
              aig
              (Decl.gateToCNF
                (.inr ⟨idx, h⟩)
                (.inr ⟨lhs, by have := aig.invariant h htip; omega⟩)
                (.inr ⟨rhs, by have := aig.invariant h htip; omega⟩)
                linv
                rinv
                ++ cnf)
        //
      Cache.IsExtensionBy cache out idx h
    } :=
  have := aig.invariant h htip
  have hmarkbound : idx < cache.marks.size := by have := cache.hmarks; omega
  let out :=
    { cache with
      marks := cache.marks.set ⟨idx, hmarkbound⟩ true
      hmarks := by simp [cache.hmarks]
      inv := by
        constructor
        · intro lhs rhs linv rinv idx hbound hmarked heq
          rw [Array.getElem_set] at hmarked
          split at hmarked
          · next heq2 =>
            simp only at heq2
            simp only [heq2] at htip
            rw [htip] at heq
            cases heq
            simp [Array.getElem_set, hl, hr]
          · have := cache.inv.hmark lhs rhs linv rinv idx hbound hmarked heq
            simp [Array.getElem_set, this]
        · intro assign heval idx hbound hmarked
          rw [Array.getElem_set] at hmarked
          split at hmarked
          · next heq =>
            dsimp only at heq
            simp only [heq, CNF.eval_append, Decl.gateToCNF_eval, Bool.and_eq_true, beq_iff_eq]
              at htip heval
            have hleval := cache.inv.heval assign heval.right lhs (by omega) hl
            have hreval := cache.inv.heval assign heval.right rhs (by omega) hr
            simp only [denote_idx_gate htip, hleval, projectRightAssign_property, hreval, heval]
          · next heq =>
            simp only [CNF.eval_append, Decl.gateToCNF_eval, Bool.and_eq_true, beq_iff_eq] at heval
            have := cache.inv.heval assign heval.right idx hbound hmarked
            rw [this]
    }
  ⟨out, IsExtensionBy_set cache out idx hmarkbound (by simp [out])⟩

/--
The key invariant about the `State` itself (without cache): The CNF we produce is always satisfiable
at `cnfSatAssignment`.
-/
def State.Inv (cnf : CNF (CNFVar aig)) : Prop :=
  ∀ (assign1 : Nat → Bool), cnf.Sat (cnfSatAssignment aig assign1)

/--
The `State` invariant always holds when we have an empty CNF.
-/
theorem State.Inv_nil : State.Inv ([] : CNF (CNFVar aig)) := by
  simp [State.Inv]

/--
Combining two CNFs for which `State.Inv` holds preserves `State.Inv`.
-/
theorem State.Inv_append (h1 : State.Inv cnf1) (h2 : State.Inv cnf2) :
    State.Inv (cnf1 ++ cnf2) := by
  intro assign1
  specialize h1 assign1
  specialize h2 assign1
  simp [CNF.sat_def] at h1 h2 ⊢
  constructor <;> assumption

/--
`State.Inv` holds for the CNF that we produce for a `Decl.const`.
-/
theorem State.Inv_constToCNF (heq : aig.decls[upper] = .const b) :
    State.Inv (aig := aig) (Decl.constToCNF (.inr ⟨upper, h⟩) b) := by
  intro assign1
  simp [CNF.sat_def, denote_idx_const heq]

/--
`State.Inv` holds for the CNF that we produce for a `Decl.atom`
-/
theorem State.Inv_atomToCNF (heq : aig.decls[upper] = .atom a) :
    State.Inv (aig := aig) (Decl.atomToCNF (.inr ⟨upper, h⟩) (.inl a)) := by
  intro assign1
  simp [CNF.sat_def, denote_idx_atom heq]

/--
`State.Inv` holds for the CNF that we produce for a `Decl.gate`
-/
theorem State.Inv_gateToCNF {aig : AIG Nat} {h}
    (heq : aig.decls[upper]'h = .gate lhs rhs linv rinv) :
    State.Inv
      (aig := aig)
      (Decl.gateToCNF
        (.inr ⟨upper, h⟩)
        (.inr ⟨lhs, by have := aig.invariant h heq; omega⟩)
        (.inr ⟨rhs, by have := aig.invariant h heq; omega⟩)
        linv
        rinv)
    := by
  intro assign1
  simp [CNF.sat_def, denote_idx_gate heq]

/--
The state to accumulate CNF clauses as we run our Tseitin transformation on the AIG.
-/
structure State (aig : AIG Nat) where
  /--
  The CNF clauses so far.
  -/
  cnf : CNF (CNFVar aig)
  /--
  A cache so that we don't generate CNF for an AIG node more than once.
  -/
  cache : Cache aig cnf
  /--
  The invariant that `cnf` has to maintain as we build it up.
  -/
  inv : State.Inv cnf

/--
An initial state with no CNF clauses and an empty cache.
-/
def State.empty (aig : AIG Nat) : State aig where
  cnf := []
  cache := Cache.init aig
  inv := State.Inv_nil

/--
State extension are `Cache.IsExtensionBy` for now.
-/
abbrev State.IsExtensionBy (state1 : State aig) (state2 : State aig) (new : Nat)
    (hnew : new < aig.decls.size) : Prop :=
  Cache.IsExtensionBy state1.cache state2.cache new hnew

theorem State.IsExtensionBy_trans_left (state1 : State aig) (state2 : State aig)
    (state3 : State aig) (h12 : IsExtensionBy state1 state2 new1 hnew1)
    (h23 : IsExtensionBy state2 state3 new2 hnew2) : IsExtensionBy state1 state3 new1 hnew1 := by
  apply  Cache.IsExtensionBy_trans_left
  · exact h12
  · exact h23

theorem State.IsExtensionBy_trans_right (state1 : State aig) (state2 : State aig)
    (state3 : State aig) (h12 : IsExtensionBy state1 state2 new1 hnew1)
    (h23 : IsExtensionBy state2 state3 new2 hnew2) : IsExtensionBy state1 state3 new2 hnew2 := by
  apply  Cache.IsExtensionBy_trans_right
  · exact h12
  · exact h23

/--
State extension is a reflexive relation.
-/
theorem State.IsExtensionBy_rfl (state : State aig) {h}
    (hmarked : state.cache.marks[idx]'h = true) :
    State.IsExtensionBy state state idx (have := state.cache.hmarks; omega) := by
  apply Cache.IsExtensionBy_rfl <;> assumption

/--
Add the CNF for a `Decl.const` to the state.
-/
def State.addConst (state : State aig) (idx : Nat) (h : idx < aig.decls.size)
    (htip : aig.decls[idx]'h = .const b) :
    { out : State aig // State.IsExtensionBy state out idx h } :=
  let ⟨cnf, cache, inv⟩ := state
  let newCnf := Decl.constToCNF (.inr ⟨idx, h⟩) b
  have hinv := toCNF.State.Inv_constToCNF htip
  let ⟨cache, hcache⟩ := cache.addConst idx h htip
  ⟨⟨newCnf ++ cnf, cache, State.Inv_append hinv inv⟩, by simp [hcache]⟩

/--
Add the CNF for a `Decl.atom` to the state.
-/
def State.addAtom (state : State aig) (idx : Nat) (h : idx < aig.decls.size)
    (htip : aig.decls[idx]'h = .atom a) :
    { out : State aig // State.IsExtensionBy state out idx h } :=
  let ⟨cnf, cache, inv⟩ := state
  let newCnf := Decl.atomToCNF (.inr ⟨idx, h⟩) (.inl a)
  have hinv := toCNF.State.Inv_atomToCNF htip
  let ⟨cache, hcache⟩ := cache.addAtom idx h htip
  ⟨⟨newCnf ++ cnf, cache, State.Inv_append hinv inv⟩, by simp [hcache]⟩

/--
Add the CNF for a `Decl.gate` to the state.
-/
def State.addGate (state : State aig) {hlb} {hrb} (idx : Nat) (h : idx < aig.decls.size)
    (htip : aig.decls[idx]'h = .gate lhs rhs linv rinv) (hl : state.cache.marks[lhs]'hlb = true)
    (hr : state.cache.marks[rhs]'hrb = true) :
    { out : State aig // State.IsExtensionBy state out idx h } :=
  have := aig.invariant h htip
  let ⟨cnf, cache, inv⟩ := state
  let newCnf :=
    Decl.gateToCNF
      (.inr ⟨idx, h⟩)
      (.inr ⟨lhs, by omega⟩)
      (.inr ⟨rhs, by omega⟩)
      linv
      rinv
  have hinv := toCNF.State.Inv_gateToCNF htip
  let ⟨cache, hcache⟩ := cache.addGate idx h htip hl hr
  ⟨⟨newCnf ++ cnf, cache, State.Inv_append hinv inv⟩, by simp [hcache]⟩

/--
Evaluate the CNF contained within the state.
-/
def State.eval (assign : CNFVar aig → Bool) (state : State aig) : Bool :=
  state.cnf.eval assign

/--
The CNF within the state is sat.
-/
def State.Sat (assign : CNFVar aig → Bool) (state : State aig) : Prop :=
  state.cnf.Sat assign

/--
The CNF within the state is unsat.
-/
def State.Unsat (state : State aig) : Prop :=
  state.cnf.Unsat

theorem State.sat_def (assign : CNFVar aig → Bool) (state : State aig) :
    state.Sat assign ↔ state.cnf.Sat assign := by
  rfl

theorem State.unsat_def (state : State aig) :
    state.Unsat ↔ state.cnf.Unsat := by
  rfl

@[simp]
theorem State.eval_eq : State.eval assign state = state.cnf.eval assign := by simp [State.eval]

@[simp]
theorem State.sat_iff : State.Sat assign state ↔ state.cnf.Sat assign := by simp [State.sat_def]

@[simp]
theorem State.unsat_iff : State.Unsat state ↔ state.cnf.Unsat := by simp [State.unsat_def]

end toCNF

/--
Convert an AIG into CNF, starting at some entry node.
-/
def toCNF (entry : Entrypoint Nat) : CNF Nat :=
  let ⟨state, _⟩ := go entry.aig entry.ref.gate entry.ref.hgate (toCNF.State.empty entry.aig)
  let cnf : CNF (CNFVar entry.aig) := [(.inr ⟨entry.ref.gate, entry.ref.hgate⟩, true)] :: state.cnf
  cnf.relabel inj
where
  inj {aig : AIG Nat} (var : CNFVar aig) : Nat :=
    match var with
    | .inl var => aig.decls.size + var
    | .inr var => var.val
  go (aig : AIG Nat) (upper : Nat) (h : upper < aig.decls.size) (state : toCNF.State aig) :
      { out : toCNF.State aig // toCNF.State.IsExtensionBy state out upper h } :=
    if hmarked : state.cache.marks[upper]'(by have := state.cache.hmarks; omega) then
      ⟨state, by apply toCNF.State.IsExtensionBy_rfl <;> assumption⟩
    else
      let decl := aig.decls[upper]
      match heq : decl with
      | .const b => state.addConst upper h heq
      | .atom a => state.addAtom upper h heq
      | .gate lhs rhs linv rinv =>
        have := aig.invariant h heq
        let ⟨lstate, hlstate⟩ := go aig lhs (by omega) state
        let ⟨rstate, hrstate⟩ := go aig rhs (by omega) lstate

        have : toCNF.State.IsExtensionBy state rstate lhs (by omega) := by
          apply toCNF.State.IsExtensionBy_trans_left
          · exact hlstate
          · exact hrstate

        let ⟨ret, hretstate⟩ := rstate.addGate upper h heq this.trueAt hrstate.trueAt
        ⟨
          ret,
          by
            apply toCNF.State.IsExtensionBy_trans_right
            · exact hlstate
            · apply toCNF.State.IsExtensionBy_trans_right
              · exact hrstate
              · exact hretstate
        ⟩

/--
The function we use to convert from CNF with explicit auxiliary variables to just `Nat` variables
in `toCNF` is an injection.
-/
theorem toCNF.inj_is_injection {aig : AIG Nat} (a b : CNFVar aig) :
    toCNF.inj a = toCNF.inj b → a = b := by
  intro h
  cases a with
  | inl =>
    cases b with
    | inl =>
      dsimp only [inj] at h
      congr
      omega
    | inr rhs =>
      exfalso
      dsimp only [inj] at h
      have := rhs.isLt
      omega
  | inr lhs =>
    cases b with
    | inl =>
      dsimp only [inj] at h
      omega
    | inr =>
      dsimp only [inj] at h
      congr
      omega

/--
The node that we started CNF conversion at will always be marked as visited in the CNF cache.
-/
theorem toCNF.go_marks :
    (go aig start h state).val.cache.marks[start]'(by have := (go aig start h state).val.cache.hmarks; omega) = true :=
  (go aig start h state).property.trueAt

/--
The CNF returned by `go` will always be SAT at `cnfSatAssignment`.
-/
theorem toCNF.go_sat (aig : AIG Nat) (start : Nat) (h1 : start < aig.decls.size) (assign1 : Nat → Bool)
    (state : toCNF.State aig) :
    (go aig start h1 state).val.Sat (cnfSatAssignment aig assign1)  := by
  have := (go aig start h1 state).val.inv assign1
  rw [State.sat_iff]
  simp [this]

theorem toCNF.go_as_denote' (aig : AIG Nat) (start) (h1) (assign1) :
    ⟦aig, ⟨start, h1⟩, assign1⟧ → (go aig start h1 (.empty aig)).val.eval (cnfSatAssignment aig assign1) := by
  have := go_sat aig start h1 assign1 (.empty aig)
  simp only [State.Sat, CNF.sat_def] at this
  simp [this]

/--
Connect SAT results about the CNF to SAT results about the AIG.
-/
theorem toCNF.go_as_denote (aig : AIG Nat) (start) (h1) (assign1) :
    ((⟦aig, ⟨start, h1⟩, assign1⟧ && (go aig start h1 (.empty aig)).val.eval (cnfSatAssignment aig assign1)) = sat?)
      →
    (⟦aig, ⟨start, h1⟩, assign1⟧ = sat?) := by
  have := go_as_denote' aig start h1 assign1
  by_cases CNF.eval (cnfSatAssignment aig assign1) (go aig start h1 (State.empty aig)).val.cnf <;> simp_all

/--
Connect SAT results about the AIG to SAT results about the CNF.
-/
theorem toCNF.denote_as_go {assign : AIG.CNFVar aig → Bool}:
    (⟦aig, ⟨start, h1⟩, projectLeftAssign assign⟧ = false)
      →
    CNF.eval assign (([(.inr ⟨start, h1⟩, true)] :: (go aig start h1 (.empty aig)).val.cnf)) = false := by
  intro h
  match heval1:(go aig start h1 (State.empty aig)).val.cnf.eval assign with
  | true =>
    have heval2 := (go aig start h1 (.empty aig)).val.cache.inv.heval
    specialize heval2 assign heval1 start h1 go_marks
    simp only [h, projectRightAssign_property, Bool.false_eq] at heval2
    simp [heval2]
  | false =>
    simp [heval1]

/--
An AIG is unsat iff its CNF is unsat.
-/
theorem toCNF_equisat (entry : Entrypoint Nat) : (toCNF entry).Unsat ↔ entry.Unsat := by
  dsimp only [toCNF]
  rw [CNF.unsat_relabel_iff]
  · constructor
    · intro h assign1
      apply toCNF.go_as_denote
      specialize h (toCNF.cnfSatAssignment entry.aig assign1)
      simpa using h
    · intro h assign
      apply toCNF.denote_as_go
      specialize h (toCNF.projectLeftAssign assign)
      assumption
  · intro a b _ _ hinj
    apply toCNF.inj_is_injection
    assumption

end AIG

end Sat
end Std
