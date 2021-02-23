% Liquid Meta: Mechanizing the Metatheory behind Liquid Haskell
% Michael Humes Borkowski
% March 12, 2021

---

## Outline / Table of Contents slide here

---

## Type Systems with Refinments / Contracts

 * A refinment type like { x:Int | 1 < x && x < 20 } is a set of values that satisfy some arbitrary predicate

 * Languages can be designed with static checking only or hybrid type checking where some checks occur at runtime.

---

## Why Refinment Types?

 * We can express precise preconditions/postconditions on functions. This can reduce runtime/uncaught errors (divide by zero, array bounds)

 * We can express invariants in the definition of data types

---

## Refinement Types

 * Our present work focuses on contracts that can be ...

---

## Big Question: Can we put the type system of Liquid Haskell on a more solid theoretical footing?
	
 * Existing published calculi: not rich enough to model LH's type system

 * Jhala and Vazou have defined a calculus but no metahtheory (yet) 

---

## Big Question: Can we put the type system of Liquid Haskell on a more solid theoretical footing?
	
#  Problem: Length and complexity of informal metatheory dramatically increases as we move from toy languages to more robust models

 * Are there any missed cases in inductive proofs? (Inversion Lemmas, etc)

 * Is there circular reasoning? (mutual structual induction that's not well-founded

---

## Big Question: Can we put the type system of Liquid Haskell on a more solid theoretical footing?
	
#  Problem: Length and complexity of informal metatheory dramatically increases as we move from toy languages to more robust models

#  Idea: A formal _mechanized_ proof checked by an automated theorem prover is an ideal way to ensure that we can have confidence in our soundness proof.

---

## Prior Work: Metatheory

## Prior Work: Mechanization

---

## Prior Metatheory: The Sage Programming Language

 * Knowles, Tomb, Gronski, Freund, Flanagan (2006 Tech Report)

 * Simply-typed Lambda Calculus with Refinement Types, Hybrid Typechecking

 * Full pen-and-paper proofs of progress and preservation 

---

## Prior Metatheory: Refinement Types for Haskell

 * Vazou, Seidel, Jhala, Vytiniotis, Peyton-Jones (2014 Tech Report)

 * Simply-typed Lambda Calculus with refinement types, laziness, data types

 * Metatheory uses denotational semantics for declarative subtyping

 * Full pen-and-paper proofs of progress and preservation

---

## Prior Metatheory: Polymorphic Manifest Contracts

 * Sekiyama, Igarashi, and Greenberg (ToPLaS 2015)

 * Polymorphic Lambda Calculus with manifest contracts

 * No static subtyping rule for refinement types: all checks for contract satisfaction deferred until runtime.

 * Detailed metatheory with a different flavor from Vazou et al
