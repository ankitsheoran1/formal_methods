-------------------------------- MODULE gcd --------------------------------
EXTENDS Integers
Divides(p,n)== \E q \in 1..n : n = q * p 
DivisorsOf(n) == { p \in Int : Divides(p,n)}
SetMax(s) == CHOOSE i \in s: \A j \in s : i >= j
GCD(m, n) == SetMax(DivisorsOf(m) /\ DivisorsOf(n))


=============================================================================
\* Modification History
\* Last modified Sun Apr 21 10:42:18 IST 2024 by ankit
\* Created Sun Apr 21 10:17:28 IST 2024 by ankit