(* begin hide *)
Require Import Unicode.Utf8.
Require Import RefTrans.Relations.Relation_Operators.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
(* end hide *)

(** * The common semantics of a ref-trans rewrite system

    The rewrite system view of ref-trans treats a set of stores as a
    #<a href="https://en.wikipedia.org/wiki/Rewriting">#rewrite system
    #</a># over a single typed term language. This class defines the
    base semantics any such set of stores will respect, regardless of
    the specific stores involved.
  *)

Class base (type : Type) (term : type → Type) :=
  { (** ** Constructs supported by the type language *)
    (** The function type former *)
    function : type → type → type;

    (** ** Constructs supported by the term language *)
    (** Variables

        The identifiers used in variables correspond, operationally,
        to the names of resources in some store.
      *)
    identifier : type → Type;
    variable : ∀ {t}, identifier t → term t;
    (** Function application *)
    apply : ∀ {a b}, term (function a b) → term a → term b;

    (** ** The rewrite rules of the system *)
    rewrites_to : ∀ {t}, term t → term t → Type;
    (** The equivalence relation given by the reflexive transitive
        closure of rewriting.
      *)
    rewrites_equivalence : ∀ {t}, relation (term t) :=
      λ t, clos_refl_sym_trans (term t) rewrites_to;
    (** We can rewrite either side of a function application. *)
    rewrite_function : ∀ {dom cod} {f f' : term (function dom cod)} {x}
                     , rewrites_to f f'
                     → rewrites_to (apply f x) (apply f' x);
    rewrite_argument : ∀ {dom cod} {f : term (function dom cod)} {x x'}
                     , rewrites_to x x'
                     → rewrites_to (apply f x) (apply f x');

    (** ** Identifying terms

        Some terms can be identified, i.e. assigned a name to be used
        in referring to the term with a variable. Operationally,
        these are the commands that can actually cause a resource to
        be realized into the store, with the identifiers being the
        keys used for caching, sharing, etc. As such, ideal
        identifiers would uniquely identify the term in question
        (up to the relevant equivalence class for non-deterministic
        stores) and be relatively cheap to compute. In practice, this
        means crypographic hashes.
      *)
     identifiable : ∀ {t}, term t → Type;
     (** Given an identifiable term, we can get an identifier that,
         when used in a variable, is equivalent under the rewrite
         relation to the original term.
       *)
     identify : ∀ {ty} (t : term ty), identifiable t →
       { i : identifier ty & rewrites_equivalence (variable i) t };
  }.
