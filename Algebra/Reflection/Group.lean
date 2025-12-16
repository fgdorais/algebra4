/-
Copyright © 2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Algebra.Instances
import Algebra.Theories.Group

open List
open Logic

namespace Algebra

namespace Group

inductive Word {α} (xs : List α)
| id : Word xs
| pos : Index xs → Word xs → Word xs
| neg : Index xs → Word xs → Word xs

namespace Word
variable {α} {xs : List α} {u v w : Word xs}

instance instDecidableEq (xs : List α) : DecidableEq (Word xs)
| id, id => isTrue rfl
| id, pos _ _ => isFalse (by grind only)
| id, neg _ _ => isFalse (by grind only)
| pos _ _, id => isFalse (by grind only)
| pos i a, pos j b =>
  match inferDecidable (i = j), instDecidableEq xs a b with
  | isTrue rfl, isTrue rfl => isTrue rfl
  | isFalse h, _ => isFalse fun | rfl => h rfl
  | _, isFalse h => isFalse fun | rfl => h rfl
| pos _ _, neg _ _ => isFalse (by grind only)
| neg _ _, id => isFalse (by grind only)
| neg _ _, pos _ _ => isFalse (by grind only)
| neg i a, neg j b =>
  match inferDecidable (i = j), instDecidableEq xs a b with
  | isTrue rfl, isTrue rfl => isTrue rfl
  | isFalse h, _ => isFalse fun | rfl => h rfl
  | _, isFalse h => isFalse fun | rfl => h rfl

def lift (x : α) : Word xs → Word (x :: xs)
| id => id
| pos i a => pos (Index.tail i) (lift x a)
| neg i a => neg (Index.tail i) (lift x a)

def rpos : Index xs → Word xs → Word xs
| i, neg j w => if i = j then w else pos i (neg j w)
| i, w => pos i w

def rneg : Index xs → Word xs → Word xs
| i, pos j w => if i = j then w else neg i (pos j w)
| i, w => neg i w

def rapp : Word xs → Word xs → Word xs
| id, w => w
| pos i v, w => rpos i (rapp v w)
| neg i v, w => rneg i (rapp v w)

def raux : Word xs → Word xs → Word xs
| id, w => w
| pos i v, w => raux v (rneg i w)
| neg i v, w => raux v (rpos i w)

abbrev rinv : Word xs → Word xs := (raux . id)

def isReduced : Word xs → Bool
| pos _ (pos j w) => isReduced (pos j w)
| pos i (neg j w) => i ≠ j && isReduced (neg j w)
| neg i (pos j w) => i ≠ j && isReduced (pos j w)
| neg _ (neg j w) => isReduced (neg j w)
| _ => true

theorem isReduced_id : (id (xs:=xs)).isReduced := rfl

theorem isReduced_pos_tail {i : Index xs} : (pos i w).isReduced → w.isReduced := by
  intro h
  match w with
  | id => rfl
  | pos _ _ => exact h
  | neg _ _ => rw [isReduced, Bool.and_eq_true_iff] at h; exact h.2

theorem isReduced_neg_tail {i : Index xs} : (neg i w).isReduced → w.isReduced := by
  intro h
  match w with
  | id => rfl
  | pos _ _ => rw [isReduced, Bool.and_eq_true_iff] at h; exact h.2
  | neg _ _ => exact h

theorem isReduced_lift {x : α} (h : w.isReduced) : (w.lift x).isReduced := by
  induction w with
  | id => rfl
  | pos i w ih =>
    match w with
    | id => rfl
    | pos _ _ => rw [lift, lift, isReduced]; exact ih (isReduced_pos_tail h)
    | neg j _ =>
      by_cases i = j with
      | isTrue rfl => simp [isReduced] at h
      | isFalse hne =>
        rw [lift, lift, isReduced, Bool.and_eq_true]
        constructor
        · apply decide_eq_true; intro | rfl => contradiction
        · exact ih (isReduced_pos_tail h)
  | neg i w ih =>
    match w with
    | id => rfl
    | pos j _ =>
      by_cases i = j with
      | isTrue rfl => simp [isReduced] at h
      | isFalse hne =>
        rw [lift, lift, isReduced, Bool.and_eq_true]
        constructor
        · apply decide_eq_true; intro | rfl => contradiction
        · exact ih (isReduced_neg_tail h)
    | neg _ _ => rw [lift, lift, isReduced]; exact ih (isReduced_neg_tail h)

theorem isReduced_rpos (h : w.isReduced) : (w.rpos i).isReduced := by
  match w with
  | id => exact h
  | pos _ _ => exact h
  | neg j _ =>
    by_cases i = j with
    | isTrue hij => simp only [rpos]; rw [if_pos hij, isReduced_neg_tail h]
    | isFalse hij => simp only [rpos]; rw [if_neg hij, isReduced, decide_eq_true hij, h]; rfl

theorem isReduced_rneg (h : w.isReduced) : (w.rneg i).isReduced := by
  match w with
  | id => exact h
  | pos j _ =>
    by_cases i = j with
    | isTrue hij => simp only [rneg]; rw [if_pos hij, isReduced_pos_tail h]
    | isFalse hij => simp only [rneg]; rw [if_neg hij, isReduced, decide_eq_true hij, h]; rfl
  | neg _ _ => exact h

theorem isReduced_rapp (h : w.isReduced) : (rapp v w).isReduced := by
  induction v with
  | id => exact h
  | pos _ _ ih => unfold rapp; apply isReduced_rpos; exact ih
  | neg _ _ ih => unfold rapp; apply isReduced_rneg; exact ih

theorem isReduced_raux (h : w.isReduced) : (raux v w).isReduced := by
  induction v generalizing w with
  | id => exact h
  | pos _ _ ih => unfold raux; apply ih; apply isReduced_rneg h
  | neg _ _ ih => unfold raux; apply ih; apply isReduced_rpos h

theorem isReduced_rinv : w.rinv.isReduced := isReduced_raux isReduced_id

theorem rinv_eq : rinv w = raux w id := rfl

theorem rpos_rneg_cancel (h : w.isReduced) : rpos i (rneg i w) = w := by
  match w with
  | id => simp [rneg, rpos]
  | pos k w =>
    unfold rneg rpos
    match inferDecidable (i = k), w with
    | isTrue rfl, id => simp
    | isTrue rfl, pos k w => simp
    | isTrue rfl, neg k w =>
      by_cases i = k with
      | isTrue rfl => simp [isReduced] at h
      | isFalse hne => simp [hne]
    | isFalse hne, _ => simp [hne]
  | neg k w => simp [rneg, rpos]

theorem rneg_rpos_cancel (h : w.isReduced) : rneg i (rpos i w) = w := by
  match w with
  | id => simp [rneg, rpos]
  | pos k w => simp [rneg, rpos]
  | neg k w =>
    unfold rneg rpos
    match inferDecidable (i = k), w with
    | isTrue rfl, id => simp
    | isTrue rfl, pos k w =>
      by_cases i = k with
      | isTrue rfl => simp [isReduced] at h
      | isFalse hne => simp [hne]
    | isTrue rfl, neg k w => simp
    | isFalse hne, _ => simp [hne]

theorem rapp_rpos_left (h : w.isReduced) : rapp (rpos i v) w = rpos i (rapp v w) := by
  match v with
  | id => rfl
  | pos j v => rfl
  | neg j v =>
    rw [rapp]
    match inferDecidable (i = j) with
    | isTrue rfl =>
      rw [rpos_rneg_cancel]
      simp only [rpos]
      rw [if_pos trivial]
      exact isReduced_rapp h
    | isFalse hne =>
      simp only [rpos]
      rw [if_neg hne, rapp, rapp]
      rfl

theorem rapp_rneg_left (h : w.isReduced) : rapp (rneg i v) w = rneg i (rapp v w) := by
  match v with
  | id => rfl
  | pos j v =>
    rw [rapp]
    match inferDecidable (i = j) with
    | isTrue rfl =>
      rw [rneg_rpos_cancel (isReduced_rapp h)]
      simp only [rneg]
      rw [if_pos trivial]
    | isFalse hne =>
      simp only [rneg]
      rw [if_neg hne, rapp, rapp]
      rfl
  | neg j v => rfl

theorem raux_rpos_left (h : w.isReduced) : raux (rpos i v) w = raux v (rneg i w) := by
  match v with
  | id => rfl
  | pos j v => rfl
  | neg j v =>
    rw [raux]
    by_cases i = j with
    | isTrue rfl =>
      rw [rpos_rneg_cancel h]
      simp only [rpos]
      rw [if_pos trivial]
    | isFalse hne =>
      simp only [rpos]
      rw [if_neg hne, raux, raux]
      rfl

theorem raux_rneg_left (h : w.isReduced) : raux (rneg i v) w = raux v (rpos i w) := by
  match v with
  | id => rfl
  | pos j v =>
    rw [raux]
    by_cases i = j with
    | isTrue rfl =>
      rw [rneg_rpos_cancel h]
      simp only [rneg]
      rw [if_pos trivial]
    | isFalse hne =>
      simp only [rneg]
      rw [if_neg hne, raux, raux]
      rfl
  | neg j v => rfl

theorem rapp_id (h : w.isReduced) : rapp w id = w := by
  induction w with
  | id => rfl
  | pos i w ih =>
    rw [rapp, ih (isReduced_pos_tail h)]
    match w with
    | id => rfl
    | pos j w => rfl
    | neg j w =>
      by_cases i = j with
      | isTrue rfl => simp [isReduced] at h
      | isFalse hne => simp only [rpos]; rw [if_neg hne]
  | neg i w ih =>
    rw [rapp, ih (isReduced_neg_tail h)]
    match w with
    | id => rfl
    | pos j w =>
      by_cases i = j with
      | isTrue rfl => simp [isReduced] at h
      | isFalse hne => simp only [rneg]; rw [if_neg hne]
    | neg j w => rfl

theorem raux_id : raux w id = rinv w := rfl

theorem rapp_assoc (h : w.isReduced) : rapp (rapp u v) w = rapp u (rapp v w) := by
  induction u with
  | id => rfl
  | pos i u ih => rw [rapp, rapp, rapp_rpos_left h, ih]
  | neg i u ih => rw [rapp, rapp, rapp_rneg_left h, ih]

theorem raux_raux_compat (h : w.isReduced) : raux (raux u v) w = raux v (rapp u w) := by
  induction u generalizing v w with
  | id => rfl
  | pos i u ih => rw [raux, rapp, ih h, raux_rneg_left (isReduced_rapp h)]; done
  | neg i u ih => rw [raux, rapp, ih h, raux_rpos_left (isReduced_rapp h)]

theorem rapp_raux_compat (h : w.isReduced) : rapp (raux u v) w = raux u (rapp v w) := by
  induction u generalizing v w with
  | id => rfl
  | pos i u ih => rw [raux, raux, ih h, rapp_rneg_left h]
  | neg i u ih => rw [raux, raux, ih h, rapp_rpos_left h]

theorem raux_rapp_compat (h : w.isReduced) : raux (rapp v u) w = raux u (raux v w) := by
  induction v generalizing u w with
  | id => rfl
  | pos j v ih => rw [raux, rapp, ←ih (isReduced_rneg h), raux_rpos_left h]
  | neg j v ih => rw [raux, rapp, ←ih (isReduced_rpos h), raux_rneg_left h]

theorem rinv_raux (h : w.isReduced) : rinv (raux w v) = raux v w := by
  rw [rinv, raux_raux_compat isReduced_id, rapp_id h]

theorem rinv_rinv (h : w.isReduced) : rinv (rinv w) = w := rinv_raux (v:=id) h

theorem rapp_eq (hv : v.isReduced) (hw : w.isReduced) : rapp v w  = raux (rinv v) w :=
  show rapp v w = raux (rinv v) (rapp id w) by rw [←rapp_raux_compat hw, ←rinv_eq, rinv_rinv hv]

theorem raux_eq (h : w.isReduced) : raux v w = rapp (rinv v) w := (rapp_raux_compat (v:=id) h).symm

theorem raux_self : raux w w = id := by
  induction w with
  | id => rfl
  | pos i w ih => simp only [raux, rneg]; rw [if_pos trivial, ih]
  | neg i w ih => simp only [raux, rpos]; rw [if_pos trivial, ih]

section Eval
variable (s : GroupSig α)

def eval : Word xs → α
| id => s.id
| pos i a => s.op i.val (eval a)
| neg i a => s.op (s.inv i.val) (eval a)

theorem eval_id : eval s (id (xs:=xs)) = s.id := rfl

theorem eval_pos (i : Index xs) (a : Word xs) : eval s (pos i a) = s.op i.val (eval s a) := rfl

theorem eval_neg (i : Index xs) (a : Word xs) : eval s (neg i a) = s.op (s.inv i.val) (eval s a) := rfl

theorem eval_lift [Group s] (a : Word xs) (x : α) : eval s (lift x a) = eval s a := by
  induction a with
  | id => rfl
  | pos i a ih => rw [lift, eval_pos, eval_pos, Index.val_tail, ih]
  | neg i a ih => rw [lift, eval_neg, eval_neg, Index.val_tail, ih]

theorem eval_rpos [Group s] (i : Index xs) (a : Word xs) : eval s (rpos i a) = s.op i.val (eval s a) := by
  match a with
  | id => rfl
  | pos j a => rfl
  | neg j a =>
    by_cases i = j with
    | isTrue rfl =>
      simp only [rpos]
      rw [if_pos trivial, eval_neg, ←op_assoc s.op, op_right_inv s.op, op_left_id s.op]
    | isFalse hne =>
      simp only [rpos]
      rw [if_neg hne, eval_pos]

theorem eval_rneg [Group s] (i : Index xs) (a : Word xs) : eval s (rneg i a) = s.op (s.inv i.val) (eval s a) := by
  match a with
  | id => rfl
  | pos j a =>
    by_cases i = j with
    | isTrue rfl =>
      simp only [rneg]
      rw [if_pos trivial, eval_pos, ←op_assoc s.op, op_left_inv s.op, op_left_id s.op]
    | isFalse hne =>
      simp only [rneg]
      rw [if_neg hne, eval_neg]
  | neg j a => rfl

theorem eval_rapp [Group s] (a b : Word xs) : eval s (rapp a b) = s.op (eval s a) (eval s b) := by
  induction a with
  | id => rw [rapp, eval_id, op_left_id s.op]
  | pos i a ih => rw [rapp, eval_pos, eval_rpos, ih, op_assoc s.op]
  | neg i a ih => rw [rapp, eval_neg, eval_rneg, ih, op_assoc s.op]

theorem eval_raux [Group s] (a b : Word xs) : eval s (raux a b) = s.op (s.inv (eval s a)) (eval s b) := by
  induction a generalizing b with
  | id => rw [raux, eval_id, inv_id s.inv, op_left_id s.op]
  | pos i a ih => rw [raux, eval_pos, ih, eval_rneg, inv_op s.inv, op_assoc s.op]
  | neg i a ih => rw [raux, eval_neg, ih, eval_rpos, inv_op s.inv, op_assoc s.op, inv_invol s.inv]

theorem eval_rinv [Group s] (a : Word xs) : eval s (rinv a) = s.inv (eval s a) := by
  rw [rinv, eval_raux, eval_id, op_right_id s.op]

end Eval

end Word

structure Expr (xs : List α) where
  word : Word xs
  isReduced : word.isReduced

namespace Expr
variable {α} {xs : List α}

protected def eq : {a b : Expr xs} → a.word = b.word → a = b
| ⟨_,_⟩, ⟨_,_⟩, rfl => rfl

instance (xs : List α) : DecidableEq (Expr xs)
| ⟨a,_⟩, ⟨b,_⟩ =>
  match inferDecidable (a = b) with
  | isTrue h => isTrue (Expr.eq h)
  | isFalse h => isFalse fun | rfl => h rfl

protected def lift (x : α) (a : Expr xs) : Expr (x :: xs) where
  word := a.word.lift x
  isReduced := Word.isReduced_lift a.isReduced

protected def id : Expr xs where
  word := Word.id
  isReduced := Word.isReduced_id

protected def pos (i : Index xs) (a : Expr xs) : Expr xs where
  word := a.word.rpos i
  isReduced := Word.isReduced_rpos a.isReduced

protected def neg (i : Index xs) (a : Expr xs) : Expr xs where
  word := a.word.rneg i
  isReduced := Word.isReduced_rneg a.isReduced

protected abbrev var (i : Index xs) : Expr xs := Expr.pos i Expr.id

protected def inv (a : Expr xs) : Expr xs where
  word := a.word.rinv
  isReduced := Word.isReduced_rinv

protected def op (a b : Expr xs) : Expr xs where
  word := a.word.rinv.raux b.word
  isReduced := Word.isReduced_raux b.isReduced

private theorem op_word_eq_rapp (a b : Expr xs) : (Expr.op a b).word = Word.rapp a.word b.word := by
  rw [Expr.op, Word.rapp_eq a.isReduced b.isReduced]

section Completeness
variable (xs : List α)

@[reducible] def sig : GroupSig (Expr xs) where
  op := Expr.op
  inv := Expr.inv
  id := Expr.id

instance : Group (sig xs) where
  op_assoc (a b c) := by apply Expr.eq; simp only [op_word_eq_rapp]; exact Word.rapp_assoc c.isReduced
  op_right_id (a) := by apply Expr.eq; exact Word.rinv_rinv a.isReduced
  op_right_inv (a) := by apply Expr.eq; exact Word.raux_self

end Completeness

section Eval
variable (s : GroupSig α) [Group s]

def eval : Expr xs → α | ⟨a,_⟩ => Word.eval s a

@[simp] theorem eval_lift (a : Expr xs) : eval s (Expr.lift x a) = eval s a := by
  simp only [Expr.lift, eval]; rw [Word.eval_lift]

@[simp] theorem eval_var (i : Index xs) : eval s (Expr.var i) = i.val := by
  simp only [Expr.pos, Expr.id, eval]; rw [Word.eval_rpos, Word.eval_id, op_right_id s.op]

omit [Group s] in
@[simp] theorem eval_id : eval s (Expr.id (xs:=xs)) = s.id := by
  simp only [Expr.id, eval]; rw [Word.eval_id]

@[simp] theorem eval_inv (a : Expr xs) : eval s (Expr.inv a) = s.inv (eval s a) := by
  simp only [Expr.inv, eval]; rw [Word.eval_rinv]

@[simp] theorem eval_op (a b : Expr xs) : eval s (Expr.op a b) = s.op (eval s a) (eval s b) := by
  simp only [Expr.op, eval]; rw [Word.eval_raux, Word.eval_rinv, inv_invol s.inv]

end Eval

end Expr

class Reflect (s : GroupSig α) (x : α) (xs : List α) where
  expr : Expr xs
  eval_eq : expr.eval s = x

protected def Reflect.eq (s : GroupSig α) (x xs) [inst : Reflect s x xs] : inst.expr.eval s = x := inst.eval_eq

namespace Reflect
variable (s : GroupSig α) [Group s]

@[simp] instance instLift (y x : α) {xs : List α} [Reflect s y xs] : Reflect s y (x :: xs) where
  expr := Expr.lift x (expr s y)
  eval_eq := by simp [eval_eq]

@[simp] instance instVar (x : α) {xs : List α} : Reflect s x (x :: xs) where
  expr := Expr.var Index.head
  eval_eq := by simp

@[simp] instance instId {xs : List α} : Reflect s (no_index s.id) xs where
  expr := Expr.id
  eval_eq := by simp

@[simp] instance instInv (x : α) {xs : List α} [Reflect s x xs] : Reflect s (no_index (s.inv x)) xs where
  expr := Expr.inv (expr s x)
  eval_eq := by simp [eval_eq]

@[simp] instance instOp (x y : α) {xs : List α} [Reflect s x xs] [Reflect s y xs] : Reflect s (no_index (s.op x y)) xs where
  expr := Expr.op (expr s x) (expr s y)
  eval_eq := by simp [eval_eq]

end Reflect

theorem reflect {α} (s : GroupSig α) [Group s] (xs : List α) {a b : α} [Reflect s a xs] [Reflect s b xs] : Reflect.expr s a (xs:=xs) = Reflect.expr s b → a = b := by
  intro h
  rw [←Reflect.eq s a xs, ←Reflect.eq s b xs, h]

end Group

end Algebra

section Example
open Algebra Notation
variable {α : Type _} (s : GroupSig α) [Group s] (a b c d : α)

local infixr:70 " ⋆ " => s.op
local postfix:max "⁻¹" => s.inv
local notation "e" => s.id

example : (a ⋆ b)⁻¹ ⋆ (c ⋆ d⁻¹) = e ⋆ b⁻¹ ⋆ ((a⁻¹ ⋆ e ⋆ c) ⋆ d⁻¹) :=
  Group.reflect s [a,b,c,d] rfl

example (x y z : Int) : x + (-y + z) + -1 = (x - (0 + y)) + z - 1 :=
  Group.reflect Int.sig.toAddGroupSig [1,x,y,z] rfl

end Example
