/-
Copyright © 2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Algebra.Instances
import Algebra.Theories.Group
import Algebra.Reflection.CommMonoid

open Logic
open List

namespace Algebra.CommGroup

inductive Expr {α : Type _} : List α → Type _
| nil : Expr []
| cons (n : Int) {x : α} {xs : List α} : Expr xs → Expr (x :: xs)

namespace Expr

instance instDecidableEq {α} : {xs : List α} → DecidableEq (Expr xs)
| [], nil, nil => Decidable.isTrue rfl
| _::_, cons m a, cons n b =>
  match instDecidableEq a b, inferDecidable (m = n) with
  | isTrue rfl, isTrue rfl => isTrue rfl
  | isFalse h, _ => isFalse fun | rfl => h rfl
  | _, isFalse h => isFalse fun | rfl => h rfl

abbrev lift {α} (x : α) {xs : List α} : Expr xs → Expr (x :: xs) := cons 0

protected def id {α} : {xs : List α} → Expr xs
| [] => nil
| _::_ => cons 0 Expr.id

protected def inv {α} : {xs : List α} → Expr xs → Expr xs
| [], _ => nil
| _::_, cons n a => cons (-n) (Expr.inv a)

protected def op {α} : {xs : List α} → Expr xs → Expr xs → Expr xs
| [], _, _ => nil
| _::_, cons m a, cons n b => cons (m + n) (Expr.op a b)

def mk {α} : {xs : List α} → CommMonoid.Expr xs → CommMonoid.Expr xs → Expr xs
| [], .nil, .nil => nil
| _::_, .cons m a, .cons n b => cons (Int.mk m n) (mk a b)

def split {α} : {xs : List α} → Expr xs → CommMonoid.Expr xs × CommMonoid.Expr xs
| [], _ => (.nil,.nil)
| _::_, cons m a =>
  match m, split a with
  | .ofNat m, (ap, an) => (.cons m ap, .cons 0 an)
  | .negSucc m, (ap, an) => (.cons 0 ap, .cons (m+1) an)

@[simp] theorem split_nil : (Expr.nil : Expr (α:=α) []).split = (.nil, .nil) := rfl

theorem split_cons {x : α} {xs : List α} (a : Expr xs) (m) : (Expr.cons m a : Expr (x :: xs)).split =
  match m, split a with
  | .ofNat m, (ap, an) => (.cons m ap, .cons 0 an)
  | .negSucc m, (ap, an) => (.cons 0 ap, .cons (m+1) an) := rfl

theorem inv_mk {α} {xs : List α} (a b : CommMonoid.Expr xs) : .inv (mk a b) = mk b a := by
  induction xs with
  | nil =>
    match a, b with
    | .nil, .nil => rfl
  | cons x xs ih =>
    match a, b with
    | .cons m a, .cons n b =>
      rw [Expr.mk]
      rw [Expr.mk]
      rw [Expr.inv]
      rw [Int.neg_mk]
      rw [ih]

theorem mk_op_mk {α} {xs : List α} (a₁ b₁ a₂ b₂ : CommMonoid.Expr xs) : .op (mk a₁ b₁) (mk a₂ b₂) = mk (.op a₁ a₂) (.op b₁ b₂) := by
  induction xs with
  | nil =>
    match a₁, a₂, b₁, b₂ with
    | .nil, .nil, .nil, .nil => rfl
  | cons x xs ih =>
    match a₁, a₂, b₁, b₂ with
    | .cons m₁ a₁, .cons m₂ a₂, .cons n₁ b₁, .cons n₂ b₂ =>
      rw [Expr.mk]
      rw [CommMonoid.Expr.op]
      rw [CommMonoid.Expr.op]
      rw [Expr.mk]
      rw [Expr.mk]
      rw [Expr.op]
      rw [Int.mk_add_mk]
      rw [ih]

theorem mk_split {α} {xs : List α} (a : Expr xs) : mk a.split.fst a.split.snd = a := by
  induction xs with
  | nil =>
    match a with
    | .nil => rfl
  | cons x xs ih =>
    match a with
    | .cons (.ofNat n) a =>
      rw [split_cons]
      rw [Expr.mk]
      rw [Int.mk_zero]
      rw [ih]
    | .cons (.negSucc n) a =>
      rw [split_cons]
      rw [Expr.mk]
      rw [Int.zero_mk_succ]
      rw [ih]

section Eval
variable {α} (s : GroupSig α)

def eval {xs : List α} (a : Expr xs) : α :=
  match a.split with
  | (ap, an) => s.op (ap.eval s.toMonoidSig) (s.inv (an.eval s.toMonoidSig))

@[simp] theorem eval_cons_zero {x : α} {xs : List α} (a : Expr xs) : eval s (Expr.cons (x:=x) 0 a) = eval s a := by
  simp only [eval, split_cons]
  match a.split with
  | (ap, an) =>
    rw [CommMonoid.Expr.eval_cons_zero]
    rw [CommMonoid.Expr.eval_cons_zero]

@[simp] theorem eval_cons_one [CommGroup s] {x : α} {xs : List α} (a : Expr xs) : eval s (Expr.cons (x:=x) 1 a) = s.op x (eval s a) := by
  simp only [eval, split_cons]
  match a.split with
  | (ap, an) =>
    rw [CommMonoid.Expr.eval_cons_zero]
    rw [CommMonoid.Expr.eval_cons_succ]
    rw [CommMonoid.Expr.eval_cons_zero]
    rw [Algebra.op_assoc s.op]

@[simp] theorem eval_cons_pos_succ [CommGroup s] {x : α} {xs : List α} (a : Expr xs) (n : Nat) : eval s (Expr.cons (x:=x) (Int.ofNat (n+1)) a) = s.op x (eval s (cons (x:=x) (Int.ofNat n) a)) := by
  simp only [eval, split_cons]
  match a.split with
  | (ap, an) =>
    rw [CommMonoid.Expr.eval_cons_succ]
    rw [Algebra.op_assoc s.op]

@[simp] theorem eval_cons_neg_succ [CommGroup s] {x : α} {xs : List α} (a : Expr xs) (n : Nat) : eval s (Expr.cons (x:=x) (Int.negSucc n) a) = s.op (s.inv x) (eval s (cons (x:=x) (Int.negOfNat n) a)) := by
  simp only [eval, split_cons, Int.negOfNat]
  match a.split, n with
  | (ap, an), 0 =>
    rw [CommMonoid.Expr.eval_cons_succ]
    rw [Algebra.inv_hom s.inv]
    rw [Algebra.op_left_comm s.op]
  | (ap, an), Nat.succ n =>
    rw [CommMonoid.Expr.eval_cons_succ]
    rw [Algebra.inv_hom s.inv]
    rw [Algebra.op_left_comm s.op]

theorem eval_mk [CommGroup s] {xs : List α} (a b : CommMonoid.Expr xs) : eval s (mk a b) = s.op (a.eval s.toMonoidSig) (s.inv (b.eval s.toMonoidSig)) := by
  induction xs with
  | nil =>
    match a, b with
    | .nil, .nil => rfl
  | cons x xs ih =>
    match a, b with
    | .cons m a, .cons n b =>
      induction m, n using Nat.recDiagOn with
      | zero_zero =>
        unfold Expr.mk
        rw [CommMonoid.Expr.eval_cons_zero]
        rw [Int.zero_mk_zero, eval_cons_zero]
        rw [ih]
        rw [CommMonoid.Expr.eval_cons_zero]
      | zero_succ n ih' =>
        unfold Expr.mk at ih' ⊢
        rw [CommMonoid.Expr.eval_cons_succ]
        rw [CommMonoid.Expr.eval_cons_zero]
        rw [Int.zero_mk_succ, eval_cons_neg_succ]
        rw [←Int.zero_mk n, ih']
        rw [CommMonoid.Expr.eval_cons_zero]
        rw [Algebra.inv_hom s.inv]
        rw [Algebra.op_left_comm s.op]
      | succ_zero m ih' =>
        unfold Expr.mk at ih' ⊢
        rw [CommMonoid.Expr.eval_cons_succ]
        rw [CommMonoid.Expr.eval_cons_zero]
        rw [Int.succ_mk_zero, eval_cons_pos_succ]
        rw [←Int.mk_zero m, ih']
        rw [CommMonoid.Expr.eval_cons_zero]
        rw [Algebra.op_assoc s.op]
      | succ_succ m n ih' =>
        unfold Expr.mk at ih' ⊢
        rw [CommMonoid.Expr.eval_cons_succ]
        rw [CommMonoid.Expr.eval_cons_succ]
        rw [Int.succ_mk_succ, ih']
        rw [Algebra.inv_hom s.inv]
        rw [Algebra.op_cross_comm s.op]
        rw [Algebra.op_right_inv s.op]
        rw [Algebra.op_left_id s.op]

theorem eval_lift {x : α} {xs : List α} (a : Expr xs) : eval s (Expr.lift x a) = eval s a := by
  rw [eval_cons_zero]

theorem eval_id [CommGroup s] : ∀ {xs : List α}, eval s (Expr.id (xs:=xs)) = s.id
| [] => by
  simp only [Expr.id, eval, split_cons, split_nil]
  rw [Algebra.op_right_inv s.op]
| _::_ => by
  unfold Expr.id
  rw [eval_cons_zero]
  rw [eval_id]

theorem eval_inv [CommGroup s] {xs : List α}  (a : Expr xs) : eval s (Expr.inv a) = s.inv (eval s a) := by
  rw [←mk_split a]
  rw [inv_mk]
  rw [eval_mk]
  rw [eval_mk]
  rw [Algebra.inv_op s.inv]
  rw [Algebra.inv_invol s.inv]

@[simp] theorem eval_op [CommGroup s] {xs : List α} (a b : Expr xs) : eval s (Expr.op a b) = s.op (eval s a) (eval s b) := by
  rw [←mk_split a, ←mk_split b]
  rw [mk_op_mk]
  rw [eval_mk]
  rw [eval_mk]
  rw [eval_mk]
  rw [CommMonoid.Expr.eval_op]
  rw [CommMonoid.Expr.eval_op]
  rw [Algebra.op_cross_comm s.op]
  rw [Algebra.inv_hom s.inv]

end Eval

section Completeness

theorem op_assoc {α} : ∀ {xs : List α} (a b c : Expr xs), Expr.op (Expr.op a b) c = Expr.op a (Expr.op b c)
| [], _, _, _ => by simp only [Expr.op]
| _::_, cons l a, cons m b, cons n c => by simp only [Expr.op, Int.add_assoc l m n, op_assoc a b c]

theorem op_comm {α} : ∀ {xs : List α} (a b : Expr xs), Expr.op a b = Expr.op b a
| [], _, _ => by simp only [Expr.op]
| _::_, cons m a, cons n b => by simp only [Expr.op, Int.add_comm m n, op_comm a b]

theorem op_right_id {α} : ∀ {xs : List α} (a : Expr xs), Expr.op a Expr.id = a
| [], nil => by simp only [Expr.op]
| _::_, cons n a => by simp only [Expr.id, Expr.op, Int.add_zero n, op_right_id a]

theorem op_right_inv {α} : ∀ {xs : List α} (a : Expr xs), Expr.op a (Expr.inv a) = Expr.id
| [], nil => by simp only [Expr.id, Expr.op]
| _::_, cons n a => by simp only [Expr.id, Expr.op, Expr.inv, Int.add_neg_self_right, op_right_inv a]

def sig {α} (xs : List α) : GroupSig (Expr xs) where
  op := Expr.op
  id := Expr.id
  inv := Expr.inv

instance {α} (xs : List α) : CommGroup (sig xs) where
  op_assoc := op_assoc
  op_comm := op_comm
  op_right_id := op_right_id
  op_right_inv := op_right_inv

end Completeness

end Expr

class Reflect {α} (s : GroupSig α) (x : α) (xs : List α) where
  expr : Expr xs
  eval_eq : expr.eval s = x

protected def Reflect.eq {α} (s : GroupSig α) (x xs) [inst : Reflect s x xs] : inst.expr.eval s = x := inst.eval_eq

namespace Reflect
variable {α} (s : GroupSig α) [CommGroup s]

class Var (x : α) (xs : List α) extends Reflect s x xs

instance (priority:=low) instVarLift (x y : α) (xs : List α) [Var s y xs] : Var s y (x :: xs) where
  expr := Expr.lift x (expr s y)
  eval_eq := by simp [eval_eq]

instance instVarSelf (x : α) (xs : List α) : Var s x (x :: xs) where
  expr := Expr.cons 1 Expr.id
  eval_eq := by rw [Expr.eval_cons_one, Expr.eval_id, Algebra.op_right_id s.op]

instance instOp (x y : α) {xs : List α} [Reflect s x xs] [Reflect s y xs] : Reflect s (no_index (s.op x y)) xs where
  expr := Expr.op (expr s x) (expr s y)
  eval_eq := by simp [eval_eq]

instance instInv (x : α) {xs : List α} [Reflect s x xs] : Reflect s (no_index (s.inv x)) xs where
  expr := Expr.inv (expr s x)
  eval_eq := by rw [Expr.eval_inv, eval_eq]

instance instId {xs : List α} : Reflect s (no_index s.id) xs where
  expr := Expr.id
  eval_eq := by rw [Expr.eval_id]

end Reflect

theorem reflect {α} (s : GroupSig α) [CommGroup s] (xs : List α) {a b : α} [Reflect s a xs] [Reflect s b xs] : Reflect.expr s a (xs:=xs) = Reflect.expr s b → a = b := by
  intro h
  rw [←Reflect.eq s a xs, ←Reflect.eq s b xs, h]

end Algebra.CommGroup

section Example
open Algebra Notation
variable {α : Type _} (s : GroupSig α) [CommGroup s]

local infixr:70 " ⋆ " => s.op
local postfix:max "⁻¹" => s.inv
local notation "e" => s.id

example (a b c d : α) : (a ⋆ b)⁻¹ ⋆ (c ⋆ d⁻¹) = e ⋆ ((c ⋆ a⁻¹ ⋆ e) ⋆ b⁻¹ ⋆ d⁻¹) :=
  CommGroup.reflect s [a,b,c,d] rfl

example (x y z : Int) : x + (-y + z) + z + -1 = z + (x - (0 + y)) + z - 1 :=
  CommGroup.reflect Int.sig.toAddGroupSig [1,x,y,z] rfl

end Example
