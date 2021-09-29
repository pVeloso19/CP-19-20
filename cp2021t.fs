module BTree

open Cp

// (1) Datatype definition -----------------------------------------------------

type BTree<'a> = Empty | Node of 'a * (BTree<'a> * BTree<'a>)

let inBTree x = either (konst Empty) (Node) x

let outBTree x =
     match x with
     | Empty -> i1 ()
     | Node (a,(t1,t2)) -> i2 (a,(t1,t2))

// (2) Ana + cata + hylo -------------------------------------------------------

let baseBTree f g x = (id -|- (f >< (g >< g))) x

let recBTree g x = (baseBTree id g) x 

let rec cataBTree a x = (a << (recBTree (cataBTree a)) << outBTree) x

let rec anaBTree g x =  (inBTree << (recBTree (anaBTree g) ) << g) x

let hyloBTree a c x = (cataBTree a << anaBTree c) x

// (3) Map ---------------------------------------------------------------------
let fmap f x = (cataBTree ( inBTree << baseBTree f id )) x

// (4) Examples ----------------------------------------------------------------

// (4.0) Inversion (mirror) ----------------------------------------------------

let invBTree x = cataBTree (inBTree <<  (id -|- (id >< swap))) x

// (4.1) Counting --------------------------------------------------------------

let countBTree x = cataBTree (either (konst 0) (succ << (uncurry (+)) << p2)) x

// (4.2) Serialization ---------------------------------------------------------

let join (x,(l,r)) = l@[x]@r

let inord x = either nil join x

let inordt x = cataBTree inord x                 //in-order traversal

let f1 (x,(l,r)) = x::l@r

let preord x = (either nil f1) x

let preordt x = cataBTree preord x               //pre-order traversal

let f2 (x,(l,r)) = l@r@[x]

let postordt x = cataBTree (either nil f2) x     //post-order traversal


//-- (4.4) Quicksort -------------------------------------------------------------
let rec part p list =
   match list with
   | head :: tail -> if p head then let (s,l) = part p tail in (head::s,l) 
                     else let (s,l) = part p tail in (s,head::l)
   | [] -> ([],[])


let qsep list =
   match list with
   | head :: tail -> i2 (head, (part ((>) head) tail))
   | [] -> i1 ()


let qSort x = hyloBTree inord qsep x

//-- (4.5) Traces ----------------------------------------------------------------
let rec membro a list = 
   match list with
   | [] -> false
   | x::xs -> if a=x then true else membro a xs

let rec union list1 list2 =
    match list2 with
    | [] -> list1
    | x::xs when membro  x list1 -> union list1 xs
    | x::xs -> (union list1 xs)@[x]

let tunion(a,(l,r)) = union (List.map (fun x -> a::x) l) (List.map (fun x -> a::x) r) 

let traces x = cataBTree (either (konst [[]]) tunion) x

//-- (4.6) Towers of Hanoi -------------------------------------------------------

let present x = inord x //-- same as in qSort

let strategy x =
   match x with
   | (d,0) -> i1()
   | (d,n) -> i2 ((n-1,d), ((not d, n-1),(not d, n-1)))

let hanoi x = hyloBTree present strategy x

//-- (5) Depth and balancing (using mutual recursion) --------------------------

let hbaldepth (a, ((b1,b2),(d1,d2))) = (b1 && b2 && (abs(d1-d2) <= 1), 1 + (max d1 d2))

let fbaldepth ((b1,d1),(b2,d2)) = ((b1,b2),(d1,d2))

let baldepth x = cataBTree (either (konst(true,1)) (hbaldepth << (id >< fbaldepth)) ) x

let balBTree x = let (s,l) = baldepth x in s 

let depthBTree x = let (s,l) = baldepth x in l 

//---------------------------- end of library ----------------------------------