------------------------------ MODULE tCommit ------------------------------
CONSTANT RM       \* The set of participating resource managers
VARIABLE rmState  \* `rmState[rm]' is the state of resource manager rm.
-----------------------------------------------------------------------------
TypeOK == 
  (*************************)
  (* The type-correctness invariant                                        *)
  (*************************)
  rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

Init ==   rmState = [rm \in RM |-> "working"]
  (*************************)
  (* The initial predicate.                                                *)
  (*************************)

canCommit == \A rm \in RM : rmState[rm] \in {"prepared", "committed"}
  (*************************)
  (* True iff all RMs are in the "prepared" or "committed" state.          *)
  (*************************)

notCommitted == \A rm \in RM : rmState[rm] # "committed" 
  (*************************)
  (* True iff neither no resource manager has decided to commit.           *)
  (*************************)
-----------------------------------------------------------------------------
(*************************)
(* We now define the actions that may be performed by the RMs, and then    *)
(* define the complete next-state action of the specification to be the    *)
(* disjunction of the possible RM actions.                                 *)
(*************************)
Prepare(rm) == /\ rmState[rm] = "working"
               /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]

Decide(rm)  == \/ /\ rmState[rm] = "prepared"
                  /\ canCommit
                  /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
               \/ /\ rmState[rm] \in {"working", "prepared"}
                  /\ notCommitted
                  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]

Next == \E rm \in RM : Prepare(rm) \/ Decide(rm)




=============================================================================
\* Modification History
\* Last modified Tue Apr 23 10:39:58 IST 2024 by ankit
\* Created Sun Apr 21 21:13:48 IST 2024 by ankit