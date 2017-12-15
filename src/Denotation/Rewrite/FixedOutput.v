(* begin hide *)
Require Import Unicode.Utf8.
Require Vectors.Vector.
Require Import RefTrans.Denotation.Rewrite.Base.
Require Import RefTrans.Denotation.Rewrite.File.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
(* end hide *)

(** * The denotation of a fixed-output file store.

    Files are realised verbatim into the store and identified by
    their hash.
  *)
Class fixed_output
  {type} {term} `(f : has_files type term)
  {hash_len : nat} (hash : list byte → Vector.t byte hash_len) :=
  { (** Arbitrary file contents can be added to the store. *)
    add_fixed : list byte → term file;
    (** The contents of a fixed file added to the store are just the
        original contents.
      *)
    add_fixed_copies : ∀ {bs}, realise (add_fixed bs) = bs;
    (** Fixed files added to the store can be identified with an
        identifier that is a function only of the file contents' hash
        and the store in question.
      *)
    add_fixed_identifiable : ∀ {bs}, identifiable (add_fixed bs);
    fixed_output_identifier : Vector.t byte hash_len → identifier file;
    add_fixed_identify_hashes : ∀ {bs},
      projT1 (identify (add_fixed bs) add_fixed_identifiable) =
      fixed_output_identifier (hash bs);
  }.
