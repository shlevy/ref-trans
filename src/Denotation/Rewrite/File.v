(* begin hide *)
Require Import Unicode.Utf8.
Require Vectors.Vector.
Require Import RefTrans.Denotation.Rewrite.Base.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
(* end hide *)

Inductive bit := O | I.

Definition byte := Vector.t bit 8.

(** * A minimal abstract denotation for stores that manage files.

    Terms of the [file] type can be realised to their contents.
    Subclasses should define term formers for terms of the [file]
    type, and provide meaningful guarantees about their realisations.

    Obviously there is more useful information about files possible,
    such as directory structure, file names, and metadata. Those
    should be added when necessary.
  *)

Class has_files {type} {term} `(b : base type term) :=
  { file : type;
    (** A file realises to its contents as a finite byte stream. *)
    realise : term file → list byte;
    (** Files can be identified. *)
    file_identifiable : identifiable file;
  }.
