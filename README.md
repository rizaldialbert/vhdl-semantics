# vhdl-semantics

How can we be sure that our hardware blocks designed in VHDL are mathematically correct? Even if we prove it mathematically on paper, how can we be sure that the proofs are indeed correct? The answer to these two questions is by using a theorem prover. 

This project chooses the [Isabelle][isabelle-link] theorem prover --- one of the most powerful theorem provers in the world. If you want to prove that a program is correct mathematically, you need to know the *semantics* of that language in which the program is written. A large part of this project consists of the formalisation of the language VHDL in the Isabelle theorem prover.

### Why use a theorem prover? 

Formal verification of hardware is definitely not a new thing. Model checking and other automated theorem proving techniques have been very powerful for formally verifying hardware designs. But we think that there is a semantic gap between how our designs look concretely (VHDL, Verilog, SystemVerilog, Cλash, Lava, Bluespec, Chisel, etc.) and how they are represented mathematically in model checkers (Transition Systems) --- let alone the state space explosion problem. 

Another reason for using a theorem prover such as Isabelle is the ability to access the vast library of formalised mathematics. Cryptographic primitives implemented in hardware such as encryption, decryption and hash function could access libraries such as _probability theory_ or _number theory_ in Isabelle. A digital  controller designed in VHDL could make use real analysis theories such as _limits_, _differentials_, and _integrals_ in Isabelle. This means that we can prove **strong properties** about our hardware designs.

### What kinds of semantics covered in this project? 

This project supports the following flavours of semantics: 

* Operational Semantics
  * Small-step semantics
  * Big-step semantics
* Axiomatic Semantics (Hoare Logic)

### Why formalises so many different styles of semantics?

Because we want to have a semantics with which is _easy to reason_ and _executable_. The operational semantics is geared towards executability while the axiomatic  semantics makes the reasoning easier. 

In the early phase of our design, we probably are not sure that our design behaves as we expect and in this situation the operational semantics comes handy. Because the operational semantics is executable, we can simulate the design **within** the Isabelle theorem prover. This is possible because we can execute ML program  **inside** the Isabelle theorem prover. After we are satisfied with the behaviour, we can then start to think of the proof that it is correct. 

Proving the correctness of a hardware design with operational semantics is painful and awkward as shown in the theory `NAND_Femto.thy`; here is where axiomatic semantics comes in handy. This semantics is heavily based on the famous Floyd--Hoare Logic for formally verifying imperative programs. Another _raison d'etre_ for axiomatic semantic is to make those who are familiar with Hoare logic comfortable proving the correctness of a VHDL program.

### Any example I can browse on? 

The formalisation is still ongoing and currently we do not have proofs of strong properties yet. But do take a look on the examples such as `NAND_Hoare.thy`, `Dflipflop.thy`, `Double_Inverter.thy`, `Indexing_Hoare.thy`, `Multiplexer_Hoare.thy`, and `Slicing Hoare.thy`. 

### Any source to learn background required in this project?

* To learn about Isabelle, check the Bible [Concrete Semantics][conc-semantics] especially Part I of the book.
* To learn about operational semantics, check Chapter 7 of [Concrete Semantics][conc-semantics].
* To learn about Hoare logic, check Chapter 12 of [Concrete Semantics][conc-semantics] and the following book.
    > Kaldewaij, Anne. Programming: The Derivation of Algorithms. 1990. Prentice-Hall, Inc.

    The invariants found in most of the examples are the instantiation of the programming techniques "_Replacing constants by variable_" found in Chapter 4 of the book by Kaldewaij.
* To learn about the semantics of VHDL, check the following three papers:
    1. [An Operational Semantics for a Subset of VHDL](https://link.springer.com/chapter/10.1007/978-1-4615-2237-9_4) by John van Tassel.
    This is the initial reference for formalising the semantics. However, we have found many bugs in the formalisation which points to the next source for formalising the semantics of VHDL.
    2. [A formalization of a subset of VHDL in the Boyer-Moore logic](https://link.springer.com/article/10.1007/BF01383871) by David Russinoff.
    The inspiration for formalising the inertial delay is taken from this paper. 
    3. [A simple denotational semantics, proof theory and a validation condition generator for unit-delay VHDL](https://link.springer.com/article/10.1007/BF01383872) by Peter Breuer et al. 
    The notion of `worldline` is taken from this paper. However, we do not follow their formalisation of Hoare logic because it involves `wait` construct which is not always synthesisable in real hardware. 

### Any limitation of this formalisation?  

1. **Every** assignment must have a non-zero delay.
2. Every program must be inside a process block.

### Installation

You only need to install the latest version of Isabelle theorem prover, i.e. [Isabelle2019][isabelle-link] and open these theories in the theorem prover. 

### Authors 

Albert Rizaldi --- Nanyang Technological University

[isabelle-link]: https://isabelle.in.tum.de/
[conc-semantics]: http://www.concrete-semantics.org/
