# Contributing to vhdl-semantics

`vhdl-sematics` is the project for formalising the hardware description language VHDL in the Isabelle theorem prover. There are two reasons why we want to do this: 

1. To verify VHDL program mechanically; 
2. To access vast mathematical library in Isabelle.

Here is a list of potential topics to improve this project. For each topic, I will provide an introduction or background to motivate the topic, explain the main problem, and list the things we should achieve ideally.

## Potential areas

1. Language features
    * _Formalise types available in VHDL but not in Isabelle such as `STD_LOGIC` or `STD_ULOGIC`, `NATURAL` and `POSITIVE`._
    * _Formalise arithmetic operators available in VHDL but not in Isabelle.  
       For example, unary minus `(-)`, unary plus `(+)`, subtraction `(-)`, multiplication `(*)`, division `(/)`, remainder `(rem)`, modulus `mod`, exponentiation `(**)`, absolute value `abs`, with variants for arguments in signed, unsigned, or mixed._ 
    * _Formalise the concepts of `ENTITY` and `ARCHITECTURE`._
    * _Pretty printing the VHDL program just as shown in [IMP2](https://www.isa-afp.org/entries/IMP2.html) (see the construct `program_spec` in the example)._

2. Operational semantics
    * _Improve the notion of time from `nat` to `nat * nat` as exemplified by the work of [Russinoff](https://link.springer.com/article/10.1007/BF01383871)._  
    There he used two natural numbers to represent time `(t1, t2) :: nat * nat`. The first element `t1` is the actual time and the second element `t2` counts how many zero delays has happened since `t1`. My hypothesis of using pairs of natural numbers `nat * nat` instead of a single natural number `nat` to formalise the notion of time is that it will remove the non-zero delay assumption in each assignment statement.

    * _Improve the performance (speed) of simulating VHDL program._   
    Previously when there is only a single value `bool`, the time performance is reasonably fast. But since the introduction of vector values, the performance has decreased substantially. My first guess for this decrease is due to the change of the way we formalise the semantics of expression, sequential statements, and concurrent statements. Previously these semantics are formalised with `fun` but now they are formalised with `inductive` definition — this is done to improve the readability of the semantics. The first step to improve the performance is to implement an equivalent `fun` for each semantics and prove their equivalences. This is the standard way to achieve both mathematical elegance and performance when we do evaluation by code. The next step is to speed up the execution by using tools developed by [Peter Lammich](http://www21.in.tum.de/~lammich/refine_tutorial.html). 
    
    * _Improve the readability (pretty-printing) the results provided by the simulator._ 
    
3. Axiomatic semantics 
    * _Reduces the number of invariants required._  
        Current Hoare logic proofs for the VHDL programs require two kinds of invariant: one when the body of the process is executed and the other when the body is not. Could we improve the Hoare logic such that we do not need to prove the second invariant? This would be helpful because for each invariant we need to prove the invariant preservation on three different levels: the sequential level, the concurrent level, and the simulation level. We also need to prove that the result of initialisation satisfies the invariant. Reducing the number of invariant means reducing the proof effort and hence increasing the usability of this framework.

4. Applications
    * _Integer arithmetics_   
        Implement and formally verify the circuits for performing addition, multiplication, division, remainder, modulus, and exponentiation. The correctness specification could either be expressed directly in Isabelle, or we could use the semantics of those operations mentioned in the language feature. Note that the latter is called equivalence checking — a well-known technique for formal verification in the hardware community. 

    * _Floating-point arithmetics_  
        Floating-point bugs such as [Pentium FDIV bug](en.wikipedia.org/wiki/Pentium_FDIV_bug) is the most oft-cited examples for motivating formal verification. There has been some [effort](https://doi.org/10.1007/11757283_8) for using theorem provers for mechanically proving that there is no bug in the *algorithm* for floating-point arithmetics, but not until the VHDL level. This contribution require implementing and formally verifying the circuits for multiplication, division, and exponentiation for floating-point in IEEE formats. [This formalisation](www.isa-afp.org/entries/IEEE_Floating_Point.html) contains useful mathematical libraries for verifying floating-point arithmetics in VHDL. 
        
    * _Cryptographic primitives_  
        Software often relies on hardware to perform cryptographic primitives such as encryption, decryption, and hashing. But there is no guarantee that the hardware implementation of those cryptographic primitives are correct. For example, [Mouha et al.](https://doi.org/10.1109/TR.2018.2847247) found bugs in several hash function implementation. This contribution solves this problem by implementing cryptographic primitives and proving their correctness. For example, a hash function implemented in VHDL should satisfy _second pre-image resistance_, _collision resistance_, and _function behaviour_ (see [Mouha et al.](https://doi.org/10.1109/TR.2018.2847247)).
        
    * _Digital signal processors_  
        Another area which we potentially could apply the technique in this framework is the implementation of Digital Signal Processing (DSP) blocks. This is relatively easier because we have a precise mathematical specification which the VHDL program must satisfy. 
        * Implement a digital controller and prove that it satisfies the controller specification in the [frequency domain representation](www.isa-afp.org/entries/Laplace_Transform.html) (i.e. z-transform). 
        * Implement [CORDIC function](https://www.springer.com/gp/book/9781447115939) function and prove its error bounds — this depends on the previous contribution on floating-point arithmetics.
        
    * _ISA compliance of general purpose processor_  
        Each instruction set architecture (ISA) has a set of instruction with the corresponding correctness condition. Some ISAs have their semantics formalised in interactive theorem prover such as HOL and Isabelle. [Fox](https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-545.html) for example has formalised ARMv6 ISA in HOL and [Hou et al.](https://www.isa-afp.org/entries/SPARCv8.html) have formalised SPARCv8 in Isabelle. Implement these ISAs in VHDL and use this framework to formally verify their compliance according to their ISA's semantics.
        
    * _Secure crypto-coprocessor or cryptoprocessor_  
        This combines the contribution in the ISA compliance above and the formally verified cryptographic primitives.
    
