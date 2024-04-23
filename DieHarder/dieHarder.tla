----------------------------- MODULE dieHarder -----------------------------
EXTENDS Integers
MIN(m, n) == IF m < n THEN m ELSE n
\* Two constant parameters jugs and Capacity 
\* we also declare the constant Goal , which will represent the number
\* of gallons of water that our generalized heros must obtain
CONSTANT Jugs, Capacity, Goal 
\* Capacity describe the capacities of the jugs by making it a function
\* The constant Capacity will be a function whose domain is the set Jugs of
\* all jugs

ASSUME /\ Goal \in Nat
       /\ Capacity \in [Jugs -> Nat \{0}]

(*************************
 --algorithm DieHarder {
    variable injug = [j \in Jugs -> 0];
    { while( TRUE )
    {
     either with( j \in Jugs) 
     { injug[j] := Capacity[j]; };
     or with ( j \in Jugs )
     { injug[j] := 0; };
     or  with (j \in Jugs, k \in Jugs \{j})
     { with ( poured = Min(injug[j ] + injug[k ], Capacity[k ]) - injug[k ]) 
        { injug[j ] := injug[j ] - poured ||
          injug[k ] := injug[k ] + poured;
        }
     }
     }
    }
    }
 *************************)     
\* BEGIN TRANSLATION (chksum(pcal) = "91dc6179" /\ chksum(tla) = "be117d35")
VARIABLE injug

TypeOK == injug \in [Jugs -> Nat]
Init == injug = [j \in Jugs |-> 0]
FillJug(j) == injug' = [injug  EXCEPT ![j] = Capacity[j]]
EmptyJug(j) == injug' = [injug  EXCEPT ![j] = 0]
\* ![] means current state 
\* EXCEPT means same Set except these condition 
\* @ means current state 
\* Spec specify here defines a temporal logic formula called , which represents a specification of a system's behavior.
\* 
JugToJug(j, k) == 
    LET poured == MIN(injug[j], Capacity[k]-injug[k])
    IN injug' = [injug EXCEPT ![j] = @ - poured,
                                   ![k] = @ + poured]
Next == \E j \in Jugs: \/FillJug(j)
                      \/ EmptyJug(j)
                      \/ \E k \in Jugs \ {j} : JugToJug(j, k)
Spec == Init /\ [][Next]_injug                      
NotSolved == \A j \in Jugs : injug[j] # Goal                                                       

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Sun Apr 21 16:09:42 IST 2024 by ankit
\* Created Mon Apr 15 15:23:30 IST 2024 by ankit