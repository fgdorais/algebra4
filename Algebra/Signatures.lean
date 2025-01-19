/-
Copyright © 2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Algebra.Basic

namespace Algebra

structure SemigroupSig (α) where
  op : α → α → α

structure MonoidSig (α) extends SemigroupSig α where
  id : α

structure GroupSig (α) extends MonoidSig α where
  inv : α → α

structure SemiringSig (α) where
  add : α → α → α
  mul : α → α → α

def SemiringSig.toAddSemigroupSig {α} (s : SemiringSig α) : SemigroupSig α where
  op := s.add

unif_hint {α} (s : SemiringSig α) (t : SemigroupSig α) where
  t =?= s.toAddSemigroupSig ⊢ t.op =?= s.add

def SemiringSig.toMulSemigroupSig {α} (s : SemiringSig α) : SemigroupSig α where
  op := s.mul

unif_hint {α} (s : SemiringSig α) (t : SemigroupSig α) where
  t =?= s.toMulSemigroupSig ⊢ t.op =?= s.mul

structure RigSig (α) extends SemiringSig α where
  zero : α

def RigSig.toAddMonoidSig {α} (s : RigSig α) : MonoidSig α where
  toSemigroupSig := s.toAddSemigroupSig
  id := s.zero

unif_hint {α} (s : RigSig α) (t : MonoidSig α) where
  t =?= s.toAddMonoidSig ⊢ t.toSemigroupSig =?= s.toAddSemigroupSig

unif_hint {α} (s : RigSig α) (t : MonoidSig α) where
  t =?= s.toAddMonoidSig ⊢ t.id =?= s.zero

structure RingSig (α) extends RigSig α where
  neg : α → α

abbrev RingSig.sub (self : RingSig α) (x y) := self.add x (self.neg y)

def RingSig.toAddGroupSig {α} (s : RingSig α) : GroupSig α where
  toMonoidSig := s.toAddMonoidSig
  inv := s.neg

unif_hint {α} (s : RingSig α) (t : GroupSig α) where
  t =?= s.toAddGroupSig ⊢ t.toMonoidSig =?= s.toAddMonoidSig

unif_hint {α} (s : RingSig α) (t : GroupSig α) where
  t =?= s.toAddGroupSig ⊢ t.inv =?= s.neg

structure UnitalSemiringSig (α) extends SemiringSig α where
  one : α

def UnitalSemiringSig.toMulMonoidSig {α} (s : UnitalSemiringSig α) : MonoidSig α where
  toSemigroupSig := s.toMulSemigroupSig
  id := s.one

unif_hint {α} (s : UnitalSemiringSig α) (t : MonoidSig α) where
  t =?= s.toMulMonoidSig ⊢ t.toSemigroupSig =?= s.toMulSemigroupSig

unif_hint {α} (s : UnitalSemiringSig α) (t : MonoidSig α) where
  t =?= s.toMulMonoidSig ⊢ t.id =?= s.one

structure UnitalRigSig (α) extends RigSig α where
  one : α

def UnitalRigSig.toUnitalSemiringSig {α} (s : UnitalRigSig α) : UnitalSemiringSig α where
  toSemiringSig := s.toSemiringSig
  one := s.one

unif_hint {α} (s : UnitalRigSig α) (t : UnitalSemiringSig α) where
  t =?= s.toUnitalSemiringSig ⊢ t.toSemiringSig =?= s.toSemiringSig

unif_hint {α} (s : UnitalRigSig α) (t : UnitalSemiringSig α) where
  t =?= s.toUnitalSemiringSig ⊢ t.one =?= s.one

structure UnitalRingSig (α) extends RingSig α where
  one : α

def UnitalRingSig.toUnitalRigSig {α} (s : UnitalRingSig α) : UnitalRigSig α where
  toRigSig := s.toRigSig
  one := s.one

unif_hint {α} (s : UnitalRingSig α) (t : UnitalRigSig α) where
  t =?= s.toUnitalRigSig ⊢ t.toRigSig =?= s.toRigSig

unif_hint {α} (s : UnitalRingSig α) (t : UnitalRigSig α) where
  t =?= s.toUnitalRigSig ⊢ t.one =?= s.one

abbrev UnitalRingSig.toUnitalSemiringSig {α} (s : UnitalRingSig α) := s.toUnitalRigSig.toUnitalSemiringSig

unif_hint {α} (s : UnitalRingSig α) (t : UnitalSemiringSig α) where
  t =?= s.toUnitalSemiringSig ⊢ t.toSemiringSig =?= s.toSemiringSig

unif_hint {α} (s : UnitalRingSig α) (t : UnitalSemiringSig α) where
  t =?= s.toUnitalSemiringSig ⊢ t.one =?= s.one

abbrev UnitalRingSig.toMulMonoidSig {α} (s : UnitalRingSig α) := s.toUnitalSemiringSig.toMulMonoidSig

unif_hint {α} (s : UnitalRingSig α) (t : MonoidSig α) where
  t =?= s.toMulMonoidSig ⊢ t.toSemigroupSig =?= s.toMulSemigroupSig

unif_hint {α} (s : UnitalRingSig α) (t : MonoidSig α) where
  t =?= s.toMulMonoidSig ⊢ t.id =?= s.one

structure SemicategorySig {α} (β : α → α → Sort _) where
  op {{a b c}} : β b c → β a b → β a c

def SemicategorySig.toSemigroupSig {α} {β : α → α → Sort _} (s : SemicategorySig β) (a : α) : SemigroupSig (β a a) where
  op := s.op (a:=a) (b:=a) (c:=a)

unif_hint {α} {β : α → α → Sort _} {a : α} (s : SemicategorySig β) (t : SemigroupSig (β a a)) where
  t =?= s.toSemigroupSig a ⊢ t.op =?= s.op (a:=a) (b:=a) (c:=a)

structure CategorySig {α} (β : α → α → Sort _) extends SemicategorySig β where
  id {a} : β a a

def CategorySig.toMonoidSig {α} {β : α → α → Sort _} (s : CategorySig β) (a : α) : MonoidSig (β a a) where
  toSemigroupSig := s.toSemigroupSig a
  id := s.id (a:=a)

unif_hint {α} {β : α → α → Sort _} {a : α} (s : CategorySig β) (t : MonoidSig (β a a)) where
  t =?= s.toMonoidSig a ⊢ t.toSemigroupSig =?= s.toSemigroupSig a

unif_hint {α} {β : α → α → Sort _} {a : α} (s : CategorySig β) (t : MonoidSig (β a a)) where
  t =?= s.toMonoidSig a ⊢ t.id =?= s.id (a:=a)

structure GroupoidSig {α} (β : α → α → Sort _) extends CategorySig β where
  inv {{a b}} : β a b → β b a

def GroupoidSig.toGroupSig {α} {β : α → α → Sort _} (s : GroupoidSig β) (a : α) : GroupSig (β a a) where
  toMonoidSig := s.toMonoidSig a
  inv := s.inv (a:=a) (b:=a)

unif_hint {α} {β : α → α → Sort _} {a : α} (s : GroupoidSig β) (t : GroupSig (β a a)) where
  t =?= s.toGroupSig a ⊢ t.toMonoidSig =?= s.toMonoidSig a

unif_hint {α} {β : α → α → Sort _} {a : α} (s : GroupoidSig β) (t : GroupSig (β a a)) where
  t =?= s.toGroupSig a ⊢ t.inv =?= s.inv (a:=a) (b:=a)

def SemigroupSig.toSemicategorySig {α} (s : SemigroupSig α) : SemicategorySig fun _ _ : Unit => α where
  op _ _ _ := s.op

unif_hint {α} (s : SemigroupSig α) (t : SemicategorySig fun _  _ : Unit => α) where
  t =?= s.toSemicategorySig ⊢ t.op (a:=()) (b:=()) (c:=()) =?= s.op

def MonoidSig.toCategorySig {α} (s : MonoidSig α) : CategorySig fun _ _ : Unit => α where
  toSemicategorySig := s.toSemicategorySig
  id := s.id

unif_hint {α} (s : MonoidSig α) (t : CategorySig fun _  _ : Unit => α) where
  t =?= s.toCategorySig ⊢ t.toSemicategorySig =?= s.toSemicategorySig

unif_hint {α} (s : MonoidSig α) (t : CategorySig fun _  _ : Unit => α) where
  t =?= s.toCategorySig ⊢ t.id (a:=()) =?= s.id

def GroupSig.toGroupoidSig {α} (s : GroupSig α) : GroupoidSig fun _ _ : Unit => α where
  toCategorySig := s.toCategorySig
  inv _ _ := s.inv

unif_hint {α} (s : GroupSig α) (t : GroupoidSig fun _  _ : Unit => α) where
  t =?= s.toGroupoidSig ⊢ t.toCategorySig =?= s.toCategorySig

unif_hint {α} (s : GroupSig α) (t : GroupoidSig fun _  _ : Unit => α) where
  t =?= s.toGroupoidSig ⊢ t.inv (a:=()) (b:=()) =?= s.inv

end Algebra
