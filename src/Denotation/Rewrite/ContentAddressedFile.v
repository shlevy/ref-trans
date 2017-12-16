(* begin hide *)
Require Import Unicode.Utf8.
Require Vectors.Vector.
Require Import RefTrans.Denotation.Rewrite.Base.
Require Import RefTrans.Denotation.Rewrite.File.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
(* end hide *)

(** * The denotation of a content-addressed file store.

    Files are realised verbatim into the store and identified by
    their hash.
  *)
Class content_addressed
  {type} {term} `(f : has_files type term)
  {hash_len : nat} (hash : list byte → Vector.t byte hash_len) :=
  { (** Arbitrary file contents can be added to the store. *)
    add_file : list byte → term file;
    (** The contents of a file added to the store are just the
        original contents.
      *)
    add_file_copies : ∀ {bs}, realise (add_file bs) = bs;
    (** Files added to the store can be identified with an
        identifier that is a function only of the file contents' hash
        and the store in question.
      *)
    add_file_identifiable : ∀ {bs}, identifiable (add_file bs);
    content_addressed_identifier : Vector.t byte hash_len
                                 → identifier file;
    add_file_identify_hashes : ∀ {bs},
      projT1 (identify (add_file bs) add_file_identifiable) =
      content_addressed_identifier (hash bs);
  }.
