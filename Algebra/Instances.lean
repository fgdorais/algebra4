/-
Copyright © 2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Algebra.Signatures
import Algebra.Identities
import Algebra.Theories

section instances
open Algebra

protected def Pos.sig : UnitalSemiringSig Pos where
  add := Pos.add
  mul := Pos.mul
  one := Pos.one

namespace Algebra.Notation

scoped instance : OfNat Pos (nat_lit 1) := ⟨Pos.sig.one⟩
scoped instance : Add Pos := ⟨Pos.sig.add⟩
scoped instance : Mul Pos := ⟨Pos.sig.mul⟩

end Algebra.Notation

instance Pos.instUnitalCommSemiring : UnitalCommSemiring Pos.sig where
  add_assoc := Pos.add_assoc
  add_comm := Pos.add_comm
  mul_assoc := Pos.mul_assoc
  mul_comm := Pos.mul_comm
  mul_right_id := Pos.mul_one
  mul_right_distrib := Pos.right_distrib

protected def Nat.sig : UnitalRigSig Nat where
  add := Nat.add
  mul := Nat.mul
  zero := Nat.zero
  one := Nat.succ Nat.zero

namespace Algebra.Notation

scoped instance : OfNat Nat (nat_lit 0) := ⟨Nat.sig.zero⟩
scoped instance : OfNat Nat (nat_lit 1) := ⟨Nat.sig.one⟩
scoped instance : Add Nat := ⟨Nat.sig.add⟩
scoped instance : Mul Nat := ⟨Nat.sig.mul⟩

end Algebra.Notation

instance Nat.instUnitalCommRig : UnitalCommRig Nat.sig where
  add_assoc := Nat.add_assoc
  add_comm := Nat.add_comm
  add_right_id := Nat.add_zero
  mul_assoc := Nat.mul_assoc
  mul_comm := Nat.mul_comm
  mul_right_id := Nat.mul_one
  mul_right_distrib := Nat.right_distrib
  mul_right_zero := Nat.mul_zero

protected def Int.sig : UnitalRingSig Int where
  add := Int.add
  mul := Int.mul
  neg := Int.neg
  zero := Int.ofNat 0
  one := Int.ofNat 1

instance Int.instUnitalCommRing : UnitalCommRing Int.sig where
  add_assoc := Int.add_assoc
  add_comm := Int.add_comm
  add_right_id := Int.add_zero
  add_right_inv := Int.sub_self
  mul_assoc := Int.mul_assoc
  mul_comm := Int.mul_comm
  mul_right_id := Int.mul_one
  mul_right_distrib := Int.add_mul

namespace Algebra.Notation

scoped instance : OfNat Int (nat_lit 0) := ⟨Int.sig.zero⟩
scoped instance : OfNat Int (nat_lit 1) := ⟨Int.sig.one⟩
scoped instance : Neg Int := ⟨Int.sig.neg⟩
scoped instance : Add Int := ⟨Int.sig.add⟩
scoped instance : Sub Int := ⟨Int.sig.sub⟩
scoped instance : Mul Int := ⟨Int.sig.mul⟩

end Algebra.Notation

end instances
