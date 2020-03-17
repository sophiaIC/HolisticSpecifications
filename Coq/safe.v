Require Import common.
Require Import loo_def.
Require Import chainmail.
Require Import loo_properties.
Require Import loo_reduction_properties.
Require Import classical_properties.
Require Import chainmail_extended_properties.
Require Import function_operations.
Require Import List.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

Module SafeExample.

  (** #<h3># Safe example: #</h3># *)
  (** ---------------------------------------------------- *)
  (** #<code># >MyModule = { #</code># *)
  (** #<code># >  Inside = {} #</code># *)
  (** #<code># >  Boundary = { #</code># *)
  (** #<code># >    field inside : Inside #</code># *)
  (** #<code># >    meth expose() = {return this.inside} #</code># *)
  (** #<code># >  } #</code># *)
  (** #<code># >} #</code># *)
  (** --------------------------------------------------- *)
  (** #<code># we want to prove: #</code># *)
  (**  *)
  (** #<code># >MyModule ⊨  #</code># *)
  (** #<code># >(∀ b, b : Boundary, ∀ i, (b.inside = i ∧ (∀ x, x access i ⇒ x = b)) #</code># *)
  (** #<code># >             ⇒ (∀ p, will⟨ p access i ⟩ #</code># *)
  (** #<code># >               ⇒ (∃ o, will⟨ o calls b.expose() ⟩))) #</code># *)
  (**  *)
  (**  *)

End SafeExample.
