------------------------ MODULE TeachingConcurrency ------------------------
EXTENDS FiniteSets, Naturals
VARIABLES x, y
CONSTANT N, NoVal
----------------------------------------------------------------------------
\* Specification based on "Teaching Concurrency"
\* found at https://lamport.azurewebsites.net/pubs/teaching-concurrency.pdf

Process == 0..(N - 1)

Value == {0, 1}

ASSUME NoVal \notin Process

TypeOk == /\ x \in [Process -> Value]
          /\ y \in [Process -> {NoVal} \cup Value]
          
\* After every process has stopped, 
\* y[i] equals 1 for at least one process i
Invariant == /\ Cardinality({p \in Process: y[p] \notin {NoVal}}) = N
                => Cardinality({p \in Process: y[p] = 1}) > 0
 
InductiveInvariant == \A p \in Process: 
                        /\ x[p] = 1 => \/ y[p] = 1        
                                       \/ \E pp \in Process: \/ x[pp] = 0
                                                             \/ y[pp] = 1
-----------------------------------------------------------------------------

Init == /\ x = [p \in Process |-> 0]
        /\ y = [p \in Process |-> NoVal]

SetNum(p) == /\ x' = [x EXCEPT ![p] = 1]
             /\ y' = [y EXCEPT ![p] = x[(p - 1) % N]]
                         
Stop == /\ \A p \in Process: y[p] \notin {NoVal}
        /\ UNCHANGED<<x, y>>

Next == \/ \E p \in Process: 
            \/ SetNum(p)
        \/ Stop

Spec  ==  Init  /\  [][Next]_<<x, y>>
-----------------------------------------------------------------------------

THEOREM  Spec  =>  [](TypeOk /\ Invariant /\ InductiveInvariant)
=============================================================================