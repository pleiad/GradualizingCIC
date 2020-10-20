This artefact contains the Agda source code accompanying the
paper ``Gradualizing the Calculus of Inductive Constructions``


# Requirements

The development relies on a recent version of Agda 
(compiles with master#cae986ea1cd51ac00faca65cd7c9dad53d0debdb
; expected to work with Agda 2.6.1 and 2.6.2).

See https://agda.readthedocs.io/en/v2.6.1/getting-started/index.html for installation instructions.

The Agda-stdlib is also required, see https://github.com/agda/agda-stdlib


# Organisation of the files

The directory `src/` contains the following files:
- `prelude.agda`: pervasives definitions
- `Poset.agda`: definition of posets, distributors (aka ep-pairs)
- `top.agda`: order structure on top
- `nat.agda`: order structure on the extended natural numbers
- `bool.agda`: order structure on the extended booleans
- `pi.agda`: order structure on monotone depdendent products

- `DiscreteModelPartial.agda`: partial discrete model
- `MaybeProp.agda`: utilities on Prop and Maybe datatypes
- `GroundTypes.agda`: head constructors of types for the monotone partial universe hierarchy
- `UnivPartial.agda`: monotone partial universe hierarchy and order on it

- `FiniteOrdinal.agda`: representation of ordinals for strong induction
- `DiscreteModelTotal.agda`: total discrete model (capturing GCIC-shift)

The subdirectory `src/Unknown` contains the development of the monotone unknown type:
- `Quotient.agda`: axiomatization of co-equalizers
- `Interface.agda`: interface for the unknown type
- `Core.agda`: definition of the quotiented unknown type
- `Rel.agda`: order on the unknown type
- `Into.agda` : definition of the heterogeneous relation into the unknown type
- `IntoRel.agda`: definition of distributors into the unknown type


# Axioms and assumptions

We use the following axioms:
- functional extensionality in `prelude.agda` (`funext`, `funext-impl`, `∀impl-ext`)
- various standard lemmas from HoTT wrt homotopy levels in `prelude.agda`; these are provable (`∀-hSet`, `∀impl-hSet`, `Σ-hset`)
- Propositional extensionality for h-propositions in `prelude.agda` (`hpropext`, `hProp-hSet`)
- the existence of coequalizers in `Unknown/Quotient.agda`
- the proof that ep-pairs for Pi-types enjoy the section-rectraction property in `pi.agda` (troubles with dependent rewrite)

We also use the following pragmas:
- `--prop`: to obtain the definitionally irrelevant hierarchy of propositions Prop
- `--without-K`: to disable UIP in pattern-matching, in order to be agnostic wrt UIP
- `--rewriting`: to add a definitional reduction rule for quotients 
- `NO_POSITIVITY_CHECK` and `TERMINATING` in `DiscreteModelPartial.agda` and `UnivPartial.agda` reflecting the non-terminating nature of these models
