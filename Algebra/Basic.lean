/-
Copyright © 2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Batteries
import Extra
import Logic

class Inv (α : Type _) where
  inv : α → α
postfix:max "⁻¹" => Inv.inv
