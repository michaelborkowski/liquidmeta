# Polymorphic Mechanization TODO list

### Definitions, Judgments, Operations
  - status: DONE
  - file: Basics.hs -- DONE
  - file: SystemFWellFormedness.hs -- DONE
  - file: SystemFTyping.hs -- DONE
  - file: WellFormedness.hs -- DONE
  - file: Typing.hs -- DONE

### Lemmas/Properties too basic to write down
  - status: mostly done
  - file: BasicPropsEnvironments.hs -- DONE
  - file: BasicPropsWellFormedness.hs -- DONE
  - file: BasicPropsDenotes.hs -- some TODO
  - file: Entailments.hs -- some cases to fill in

### System F Lemmas (not covered in pen and paper)
  - System F Lemma 1 (Primitives)  -- DONE
  - file: PrimitvesFTyping.hs -- DONE

  - System F Lemma 4 (change of vars, weakening) -- many cases todo
  - file: SystemFLemmasWellFormed.hs -- many cases TODO
  - file: SystemFLemmasFTyping.hs -- many cases TODO

  - System F Lemma 13 (Substitution) -- many cases to do
  - file: SystemFSubstitution.hs -- many cases TODO

  - System F Thm 17-18 (Progress & Preservation)	DONE
  - file: SystemFSoundness.hs			DONE

### Lemma 1 (Primitives)
  1. Well Formedness of Primitives 
    - status: DONE or assumed, TODO: add polymorphic Leq
    - files: PrimitivesWFType.hs, PrimitivesWFType*.hs -- DONE exc. Leq

  2. Denotations of Primitives
    - status: DONE or assumed, add polymorphic Leq
    - file: PrimitiveSemantics.hs -- DONE
    - files: PrimitivesDenotations.hs, PrimitivesDenotations*.hs -- DONE

  3. typing of delta(c, v)
    - status: all assumed
    - file: PrimitivesRefinements.hs -- DONE
    - file: PrimitivesDeltaTyping.hs -- mark as assumed

### Lemma 2 (Values preserved under substitution)
  - status: DONE
  - file: BasicPropsSubstitution.hs -- DONE

### Lemma 3 (Deterministic Operational Semantics)
  - status: DONE
  - file: Semantics.hs -- DONE

### Lemma 4 (Weakenings)
  - status: several cases TODO
  - file: LemmasWeakenWF.hs -- cases todo
  - file: LemmasWeakenEnt.hs -- DONE
  - file: LemmasWeakenTyp.hs -- cases todo

  - not included: Change of Variables Lemmas
  - status: several cases TODO
  - file: LemmasChangeVarWF.hs -- cases todo
  - file: LemmasChangeVarWFEnv.hs -- cases todo
  - file: LemmasChangeVarEnt.hs  -- one case todo
  - file: LemmasChangeVarTyp.hs -- cases todo

### Lemma 5 (Reflexivity of Subtyping)
  - status: TODO
  - file: LemmasSubtyping.hs -- some cases todo

### Lemma 6 (Erasure of types)
  - status: one case TODO
  - file: BasicPropsCSubst.hs -- one case, basic properties TODO

### Lemma 7 (Selfification and Denotations)
  - status: TODO (two cases)
  - file: DenotationsSelfify.hs -- cases todo

### Lemma 8 (Denotational Soundness)
  - status: TODO polymorphic cases
  - file: DenotationsSoundnessSub.hs
  - file: DenotationsSoundnessTyp.hs

### Lemma 9 (Exact Typing)
  - status: TODO most cases
  - file: LemmasExactness.hs -- most cases TODO

### Lemma 10 (Substitution Lemma)
  - status: several cases remaining
  - file: SubstitutionLemmaWF.hs
  - file: SubstitutionLemmaEnt.hs
  - file: SubstitutionLemmaTyp.hs

### Lemma 11 (Well-Formedness from Typing)
  - status: polymorphic cases TODO
  - file: LemmasTyping.hs

### Lemma 12 (Witness subtyping)
  - status: DONE
  - file: in SubstitutionLemmaWF.hs

### Lemma 13 (Narrowing of judgements)
  - status: many cases todo
  - file: part of LemmasWellFormedness.hs -- ?? TODO
  - file: LemmasNarrowingEnt.hs -- 6 TODO
  - file: LemmasNarrowingTyp.hs -- 29 TODO

### Lemma 14 (Transitivity of subtyping) 
  - status: almost done
  - file: LemmasTransitive.hs -- TODO: termination/totality

### Lemma 15 (Subtyping own transitive/reflexive closure)
  - status: DONE
  - file: LemmasSubtypeClosed.hs -- DONE

### Lemma 16 (Inversion of some typing judgments)
  - status:  DONE
  - file: LemmasInvertLambda.hs -- DONE

### Theorem 17 (Progress)		
  - status: DONE
  - file: MainTheorems.hs  --  DONE

### Theorem 18 (Preservation)	
  - status: DONE
  - file: MainTheorems.hs	 -- DONE

### Theorem 19/20 (Crash-free)
  - status: DONE
  - file: MainTheorems.hs	 -- DONE