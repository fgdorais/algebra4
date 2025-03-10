/-
Copyright © 2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Algebra.Theories.Basic
import Algebra.Theories.Group
import Algebra.Theories.Semiring
import Algebra.Theories.Rig
import Algebra.Theories.UnitalSemiring

namespace Algebra
variable {α} (s : UnitalRigSig α)

local infixr:65 " ⊹ " => s.add
local notation "𝟘" => s.zero
local infixr:70 " ⋆ " => s.mul
local notation "𝟙" => s.one

class UnitalRig : Prop extends Rig (no_index s.toRigSig), UnitalSemiring (no_index s.toUnitalSemiringSig)

protected def UnitalRig.infer [OpAssoc s.add] [OpComm s.add] [OpRightId s.add s.zero] [OpAssoc s.mul] [OpLeftDistrib s.mul s.add] [OpRightDistrib s.mul s.add] [OpLeftId s.mul s.one] [OpRightId s.mul s.one] [OpLeftNil s.mul s.zero] [OpRightNil s.mul s.zero] : UnitalRig s where
  add_assoc := op_assoc _
  add_comm := op_comm _
  add_right_id := op_right_id _
  mul_assoc := op_assoc _
  mul_left_distrib := op_left_distrib _
  mul_right_distrib := op_right_distrib _
  mul_left_id := op_left_id _
  mul_right_id := op_right_id _
  mul_left_zero := op_left_nil _
  mul_right_zero := op_right_nil _

namespace UnitalRig
variable {s} [self : UnitalRig s]

end UnitalRig

class UnitalCommRig : Prop extends CommRig (no_index s.toRigSig), UnitalCommSemiring (no_index s.toUnitalSemiringSig)

protected def UnitalCommRig.infer [OpAssoc s.add] [OpComm s.add] [OpRightId s.add s.zero] [OpAssoc s.mul] [OpComm s.mul] [OpRightDistrib s.mul s.add] [OpRightId s.mul s.one] [OpRightNil s.mul s.zero] : UnitalCommRig s where
  add_assoc := op_assoc _
  add_comm := op_comm _
  add_right_id := op_right_id _
  mul_assoc := op_assoc _
  mul_comm := op_comm _
  mul_right_distrib := op_right_distrib _
  mul_right_id := op_right_id _
  mul_right_zero := op_right_nil _

namespace UnitalCommRig
variable {s} [self : UnitalCommRig s]

end UnitalCommRig

class CancelUnitalRig : Prop extends CancelRig (no_index s.toRigSig), UnitalSemiring (no_index s.toUnitalSemiringSig)

protected def CancelUnitalRig.infer [OpAssoc s.add] [OpComm s.add] [OpRightId s.add s.zero] [OpRightCancel s.add] [OpAssoc s.mul] [OpLeftDistrib s.mul s.add] [OpRightDistrib s.mul s.add] [OpLeftId s.mul s.one] [OpRightId s.mul s.one] [OpLeftNil s.mul s.zero] [OpRightNil s.mul s.zero] : CancelUnitalRig s where
  add_assoc := op_assoc _
  add_comm := op_comm _
  add_right_id := op_right_id _
  add_right_cancel := op_right_cancel _
  mul_assoc := op_assoc _
  mul_left_distrib := op_left_distrib _
  mul_right_distrib := op_right_distrib _
  mul_left_id := op_left_id _
  mul_right_id := op_right_id _

namespace CancelUnitalRig
variable {s} [self : CancelUnitalRig s]

end CancelUnitalRig

class CancelUnitalCommRig : Prop extends CancelCommRig (no_index s.toRigSig), UnitalCommSemiring (no_index s.toUnitalSemiringSig)

protected def CancelUnitalCommRig.infer [OpAssoc s.add] [OpComm s.add] [OpRightId s.add s.zero] [OpRightCancel s.add] [OpAssoc s.mul] [OpComm s.mul] [OpRightDistrib s.mul s.add] [OpRightId s.mul s.one] [OpRightNil s.mul s.zero] : CancelUnitalCommRig s where
  add_assoc := op_assoc _
  add_comm := op_comm _
  add_right_id := op_right_id _
  add_right_cancel := op_right_cancel _
  mul_assoc := op_assoc _
  mul_comm := op_comm _
  mul_right_distrib := op_right_distrib _
  mul_right_id := op_right_id _

namespace CancelUnitalCommRig
variable {s} [self : CancelUnitalCommRig s]

end CancelUnitalCommRig

end Algebra
