------------------------------ MODULE dieHard ------------------------------
EXTENDS Integers
VARIABLES big, small
TypeOK == /\ big \in 0..5
         /\ small \in 0..3
Min(m,n) ==  IF m < n THEN m ELSE n     
FillSmall == small' = 3 /\ big' = big 
FillLarge == big' = 5 /\ small'= small
EmptyBig ==  big' = 0 /\ small' = small 
EmptySmall == small' = 0 /\ big' = big 
SmallToBig == (big' = Min(small + big, 5)) /\ (small' = small - (big' - big))
BigToSmall == (small' = Min(small + big, 3)) /\ (big' = big - (small' -small))          
Init == big = 0 /\ small = 0
Next == \/ FillSmall
        \/ FillLarge
        \/ EmptyBig
        \/ EmptySmall
        \/ SmallToBig
        \/ BigToSmall

Stop == big # 4        


=============================================================================
\* Modification History
\* Last modified Sun Apr 14 16:10:47 IST 2024 by ankit
\* Created Sun Apr 14 15:51:21 IST 2024 by ankit