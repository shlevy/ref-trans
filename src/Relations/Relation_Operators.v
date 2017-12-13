(* begin hide *)
Require Import Unicode.Utf8.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
(* end hide *)

(** * Operators over relations.

    Taken from Coq.Relations.Relation_Operators, but not limited to
    relations in [Prop].
  *)

(** A relation over a given type. *)
Definition relation (A : Type) := A → A → Type.

Section Reflexive_Symmetric_Transitive_Closure.
  Variable A : Type.
  Variable R : relation A.

  (** The reflexive symmetric transitive closure of a relation. *)
  Inductive clos_refl_sym_trans : relation A :=
    | rst_step : ∀ {x y}, R x y → clos_refl_sym_trans x y
    | rst_refl : ∀ {x}, clos_refl_sym_trans x x
    | rst_sym : ∀ {x y}
              , clos_refl_sym_trans x y
              → clos_refl_sym_trans y x
    | rst_trans : ∀ {x y z}
                , clos_refl_sym_trans x y
                → clos_refl_sym_trans y z
                → clos_refl_sym_trans x z.
End Reflexive_Symmetric_Transitive_Closure.
