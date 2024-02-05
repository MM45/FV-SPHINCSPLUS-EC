(* - Require/Import - *)
(* -- Built-In (Standard Library) -- *)
require import AllCore List Distr RealExp StdOrder.
(*---*) import IntOrder.


(* -- Local -- *)
require import BinaryTrees MerkleTrees.
require (*--*) KeyedHashFunctions TweakableHashFunctions HashAddresses.
require (*--*) DigitalSignatures.
require (*--*) FORS_TW FL_XMSS_MT_TW.



(* - Parameters - *)
(* 
  Length (in bytes) of messages as well as the length of elements of 
  private keys, public keys, and signatures
*)
const n : { int | 1 <= n } as ge1_n.

(* Base 2 logarithm of the Winternitz parameter w *)
const log2_w : { int | log2_w = 2 \/ log2_w = 4 \/ log2_w = 8 } as val_log2w.

(* Winternitz parameter (base/radix) *)
const w = 2 ^ log2_w. 

(* Length of the message in base/radix w *)
const len1 : int = ceil ((8 * n)%r / log2 w%r).

(* Length of the checksum in base/radix w *)      
const len2 : int = floor (log2 ((len1 * (w - 1))%r) / log2 w%r) + 1.

(* Number of elements (of length n) in private keys, public keys, and signatures *)
const len : int = len1 + len2.

(* Height of a single inner tree *)
const h' : { int | 1 <= h' } as ge1_hp. 

(* Number of WOTS-TW instances of a single inner tree (i.e., number of leaves) *)
const l' = 2 ^ h'.

(* Number of layers in the hypertree (i.e., height of tree of XMSS trees) *)
const d : { int | 1 <= d } as ge1_d.

(* 
  Height of "flattened" hypertree 
  (i.e., total height of concatenation of inner trees) 
*)
const h : int = h' * d.

(* 
  Number of leaves of "flattened" hypertree
  (i.e., total number of leaves of all inner trees on bottom layer)
*)
const l : int = 2 ^ h.
 
(* Address type for chaining (used in tweakable hash function calls of WOTS-TW chains) *)
const chtype : int.

(* 
  Address type for public (WOTS-TW) key compression 
  (used in tweakable hash function calls of WOTS-TW public key compression) 
*)
const pkcotype : int.

(* 
  Address type for tree hashing in the hypertree 
  (used in tweakable hash function calls of inner trees) 
*)
const trhmtype : int.

(* 
  Address type for tree hashing in FORS-TW trees
  (used in tweakable hash function calls of FORS-TW trees)
*)
const trhftype : int.

(* 
  Address type for (FORS-TW) tree root compression
  (used in tweakable hash function calls of FORS-TW tree root compression)
*)
const trcotype : int.


(* -- Properties of parameters -- *)
(* The different address types are distinct *)
axiom dist_adrstypes : uniq [chtype; pkcotype; trhmtype; trhftype; trcotype].

(* l' is greater than or equal to 2 *)
lemma ge2_lp : 2 <= l'.
proof. by rewrite /l' ler_eexpr; smt(ge1_hp). qed.

(* h is greater than or equal to 1 *)
lemma ge1_h : 1 <= h.
proof. by rewrite /h mulr_ege1 1:ge1_hp ge1_d. qed.

(* l is greater than or equal to 2 *)
lemma ge2_l : 2 <= l.
proof. by rewrite /l ler_eexpr; smt(ge1_h). qed.



(* - Operators - *)
(* -- Validity checks for (indices corresponding to) XMSS-MT-TW addresses -- *)
(* Layer index validity check (note: regards hypertree) *)
op valid_lidx (lidx : int) : bool = 
  0 <= lidx < d.

(* 
  Tree index validity check
  (Note: regards hypertree; i.e., is tidx a valid index for pointing to a tree in layer lidx) 
*)
op valid_tidx (lidx tidx : int) : bool = 
  0 <= tidx < nr_trees lidx.

(* Type index validity check *)
op valid_typeidx (typeidx : int) : bool =
  typeidx = chtype \/ typeidx = pkcotype \/ typeidx = trhtype.

(* Key pair index validity check (note: regards inner tree) *)
op valid_kpidx (kpidx : int) : bool =
  0 <= kpidx < l'.

(* Tree height index validity check (note: regards inner tree) *)
op valid_thidx (thidx : int) : bool = 
  0 <= thidx <= h'.
  
(* Tree breadth index validity check (note: regards inner tree) *)
op valid_tbidx (thidx tbidx : int) : bool = 
  0 <= tbidx < nr_nodes thidx.

(* Chain index validity check *)
op valid_chidx (chidx : int) : bool =
  0 <= chidx < len.

(* Hash index validity check *)
op valid_hidx (hidx : int) : bool = 
  0 <= hidx < w - 1.

(* Chaining address indices validity check (local part) *) 
op valid_xidxvalslpch (adidxs : int list) : bool =
     valid_hidx (nth witness adidxs 0) 
  /\ valid_chidx (nth witness adidxs 1)
  /\ valid_kpidx (nth witness adidxs 2)
  /\ nth witness adidxs 3 = chtype
  /\ valid_tidx (nth witness adidxs 5) (nth witness adidxs 4)
  /\ valid_lidx (nth witness adidxs 5).

(* Public-key compression address indices validity check (local part) *)  
op valid_xidxvalslppkco (adidxs : int list) : bool =
     nth witness adidxs 0 = 0 
  /\ nth witness adidxs 1 = 0
  /\ valid_kpidx (nth witness adidxs 2)
  /\ nth witness adidxs 3 = pkcotype
  /\ valid_tidx (nth witness adidxs 5) (nth witness adidxs 4)
  /\ valid_lidx (nth witness adidxs 5).

(* Tree hashing address indices validity check (local part)*)  
op valid_xidxvalslptrh (adidxs : int list) : bool =
     valid_tbidx (nth witness adidxs 1) (nth witness adidxs 0)
  /\ valid_thidx (nth witness adidxs 1)
  /\ nth witness adidxs 2 = 0
  /\ nth witness adidxs 3 = trhtype
  /\ valid_tidx (nth witness adidxs 5) (nth witness adidxs 4)
  /\ valid_lidx (nth witness adidxs 5).

(* Local address indices validity check *)
op valid_xidxvalslp (adidxs : int list) : bool =
  valid_xidxvalslpch adidxs \/ valid_xidxvalslppkco adidxs \/ valid_xidxvalslptrh adidxs.
