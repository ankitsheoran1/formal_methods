\* Last modified Sun Apr 21 11:52:27 IST 2024 by ankit
\* Created Sun Apr 21 11:30:37 IST 2024 by ankit
------------------------------ MODULE gcdalgo ------------------------------
EXTENDS Integers, gcd
CONSTANTS M, N
ASSUME /\ M \in Nat \ {0}
       /\ N \in Nat \ {0}

(*************************
  --algorithm Euclid {
  variables x = M, y = N;
  { while (x # y) { 
    if (x < y) { y := y - x }
    else { x := x - y }
  }
  }
  }
assert (x = y) /\ (x = GCD(x0, y0))
 *************************)
\* BEGIN TRANSLATION (chksum(pcal) = "aba70d42" /\ chksum(tla) = "79c75d9b")
VARIABLES x, y, pc

vars == << x, y, pc >>

Init == (* Global variables *)
        /\ x = M
        /\ y = N
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF x # y
               THEN /\ IF x < y
                          THEN /\ y' = y - x
                               /\ x' = x
                          ELSE /\ x' = x - y
                               /\ y' = y
                    /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << x, y >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================