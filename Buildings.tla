----------------------------- MODULE Buildings -----------------------------
CONSTANTS       \* Define the world
    People,     \* All people to manage
    Buildings   \* All buildings to manage

Outside == CHOOSE x : x \notin People \union Buildings \* Create a value for being outside a building
(*
    using \notin People \union Buildings creates a unique value,
    that is guaranteed to be in either People or Buildings
*)

VARIABLES       \* Define a state
    register,   \* set of registered people
    permission, \* function giving permisions
    location    \* function giving locations

TypeOK == 
    /\ register \subseteq People                                \* register is a subset of all people
    /\ permission \in [register -> SUBSET Buildings]            \* permission is a function from People to some subset of Buildings
    /\ location \in [register -> (Buildings \union {Outside})]  \* location is a function from People to a Building or outside

--------
Init == 
    /\ register = {}       \* register is empty set
    /\ permission = << >>  \* permission is empty function
    /\ location   = << >>  \* location is empty function

Register(p) == 
    /\ p \in People \ register                   \* p is a person not in the register
    /\ register' = register \union {p}           \* adds p to the register
    /\ permission' =                             \* update permissions 
        [x \in DOMAIN permission \union {p} |->  \* is a function from new set of registered people 
             IF x \in DOMAIN permission          \* x is already registered
             THEN permission[x]                  \* use existing permission
             ELSE {}                             \* new person has no permissions
        ]
    /\ location' =                               \* update permissions 
        [x \in DOMAIN location \union {p} |->    \* is a function from new set of registered people 
             IF x \in DOMAIN location            \* x is already registered
             THEN location[x]                    \* use existing location
             ELSE Outside                        \* new person is outside
        ]

Enter(p,b) ==                                 \* Person p enters building b
    /\ p \in register                         \* is person registered
    /\ b \in permission[p]                    \* does p have permission to enter b
    /\ location' = [location EXCEPT ![p] = b] \* update p's location
    /\ UNCHANGED register                     \* don't touch the register
    /\ UNCHANGED permission                   \* don't touch the permissions


Leave(p,b) == \* Person p leaves building b
    /\ p \in register                                 \* is person registered
    /\ location[p] = b                                \* is person p in building b
    /\ location' = [location EXCEPT ![p] = Outside]   \* update p's location
    /\ UNCHANGED <<register,permission>>              \* don't touch the register and permissions

----------
Next == \E p \in People, b \in Buildings : \* There is a person and a builing that:
    \/ Register(p)    \* the person can be registered, or
    \/ Enter(p,b)     \* the person can enter the building
    \/ Leave(p,b)     \* the person can leave the building

=============================================================================
\* Modification History
\* Last modified Wed Oct 02 12:39:11 BST 2019 by alun
\* Created Wed Oct 02 12:01:41 BST 2019 by alun
