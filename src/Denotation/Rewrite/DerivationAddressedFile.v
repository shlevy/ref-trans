(* begin hide *)
Require Import Unicode.Utf8.
Require Vectors.Vector.
Require Strings.String.

Require Import RefTrans.Denotation.Rewrite.Base.
Require Import RefTrans.Denotation.Rewrite.File.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
(* end hide *)

Record derivation :=
  { program : String.string;
    args : Datatypes.list String.string
  }.

Class derivation_addressed
  {type} {term} `(f : has_files type term)
  (derive_semantics : derivation → list byte + term file)
  {hash_len : nat} (hash : list byte → Vector.t byte hash_len) :=
  { string : type;
    string_literal : String.string → term string;
    interpolate_identifier : ∀ {ty}
                           , identifiable ty
                           → term (function ty string);
    string_append : term (function string (function string string));
    stringify_identifier : ∀ {ty}, identifier ty → String.string;
    eval_string : term string → String.string;
    eval_string_literal : ∀ {s}, eval_string (string_literal s) = s;
    eval_string_interpolate : ∀ {ty} {i : identifiable ty} {t}, eval_string (apply (interpolate_identifier i) t) = stringify_identifier (projT1 (identify t i));
    eval_string_append : ∀ {s1 s2}, eval_string (apply (apply string_append s1) s2) = String.append (eval_string s1) (eval_string s2);

    list : type → type;
    nil : ∀ {ty}, term (list ty);
    cons : ∀ {ty}, term (function ty (function (list ty) (list ty)));
    eval_list : 

    derive : term (function string (function (list string) file));
    derivation_addressed_identifier : derivation → identifier file;
    
  }.
