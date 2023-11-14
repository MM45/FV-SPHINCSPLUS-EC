(* - Require/Import - *)
(* -- Built-In (Standard Library) -- *)
require import AllCore List Distr FinType BitEncoding.
(*---*) import BS2Int.


(* -- Local -- *)
require import MerkleTrees.
require (*--*) KeyedHashFunctions TweakableHashFunctions HashAddresses.



(* - Parameters - *)
(* Length of addresses used in tweakable hash functions (including unspecified global/context part) *)
const adrs_len : { int | 4 <= adrs_len} as ge4_adrslen.

(* Byte-length of each private key element, public key element, and signature element *)
const n : { int | 1 <= n } as ge1_n.

(* Number of private key sets and merkle trees *)
const k : { int | 1 <= k } as ge1_k.

(* Height of each merkle tree *)
const a : { int | 1 <= a } as ge1_a.

(* Number of elements in each private key set and leaves in each merkle tree *)
const t : int = 2 ^ a.

(* Address type for tree hashing *)
const trhtype : int.

(* Address type for tree root compression *)
const trcotype : int.


(* -- Properties of parameters -- *)
(* The different address types are distinct *)
axiom dist_adrstypes : trhtype <> trcotype. 



(* - Types - *)
(* -- General -- *)
(* Secret seeds *)
type sseed.

(* Public seeds *)
type pseed.

(* 
  Digests, i.e., outputs of (tweakable) hash functions. 
  In fact, also input of (tweakable) hash functions in this case.
*)
type dgst = bool list.

(* Digests with length 1 (block of 8 * n bits) *)
clone import Subtype as DigestBlock with
  type T   <- dgst,
    op P x <- size x = 8 * n
    
  proof *.
  realize inhabited by exists (nseq (8 * n) witness); smt(size_nseq ge1_n).
  
type dgstblock = DigestBlock.sT.

(* Finiteness of dgstblock *)
clone import FinType as DigestBlockFT with
  type t <= dgstblock,
  
    op enum <= map DigestBlock.insubd (map (int2bs (8 * n)) (range 0 (2 ^ (8 * n))))
    
  proof *.
  realize enum_spec.
    move=> m; rewrite count_uniq_mem 1:map_inj_in_uniq => [x y | |].
    + rewrite 2!mapP => -[i [/mem_range rng_i ->]] -[j [/mem_range rng_j ->]] eqins. 
      rewrite -(DigestBlock.insubdK (int2bs (8 * n) i)) 1:size_int2bs; 1: smt(ge1_n).
      rewrite -(DigestBlock.insubdK (int2bs (8 * n) j)) 1:size_int2bs; 1: smt(ge1_n). 
      by rewrite eqins. 
    + rewrite map_inj_in_uniq => [x y /mem_range rng_x /mem_range rng_y|].
      rewrite -{2}(int2bsK (8 * n) x) 3:-{2}(int2bsK (8 * n) y) //; 1,2: smt(ge1_n).
      by move=> ->. 
    + by rewrite range_uniq.
    rewrite -b2i1; congr; rewrite eqT mapP. 
    exists (DigestBlock.val m).
    rewrite DigestBlock.valKd mapP /=. 
    exists (bs2int (DigestBlock.val m)).
    rewrite mem_range bs2int_ge0 /= (: 8 * n = size (DigestBlock.val m)) 1:DigestBlock.valP //. 
    by rewrite bs2intK bs2int_le2Xs.
  qed.


(* -- FORS-TW specific -- *)
(* Public keys *)
type pkFORSTW = dgstblock.

(* Secret keys *)
type skFORSTW = dgstblock.

(* Messages *)
clone import Subtype as MsgFORSTW with
  type T   <- bool list,
    op P l <- size l = k * a
    
  proof *.
  realize inhabited by exists (nseq (k * a) witness); smt(size_nseq ge1_k ge1_a).

type msgFORSTW = MsgFORSTW.sT.

(* Lists of length a containing digests with length 1 (block of 8 * n bits) *)
clone import Subtype as DBAL with
  type T   <- dgstblock list,
    op P l <- size l = a
    
  proof *.
  realize inhabited by exists (nseq a witness); smt(size_nseq ge1_a).
   
(* Authentication paths in merkle trees *)
type apFORSTW = DBAL.sT.

(* Lists of length k containing skFORSTW/apFORSTW pairs *)
clone import Subtype as SKAPKL with
  type T   <- (skFORSTW * apFORSTW) list,
    op P l <- size l = k
    
  proof *.
  realize inhabited by exists (nseq k witness); smt(size_nseq ge1_k).

(* Signatures *)
type sigFORSTW = SKAPKL.sT.



(* - Operators - *)
(* -- Auxiliary -- *)
(* Number of nodes in a merkle tree (of total height a) at a particular height a' *)
op nr_nodes (a' : int) = 2 ^ (a - a').


(* -- Validity checks -- *)
(* Type index validity check *)
op valid_typeidx (typeidx : int) : bool =
  typeidx = trhtype \/ typeidx = trcotype.

(* Keypair index validity check *)
op valid_kpidx (kpidx : int) : bool = 
  0 <= kpidx < k.

(* Tree height index validity check *)
op valid_thidx (thidx : int) : bool = 
  0 <= thidx <= a.

(* Tree breadth index validity check *)
op valid_tbidx (thidx tbidx : int) : bool = 
  0 <= tbidx < nr_nodes thidx.

(* Overall (generic) validity check for indices of addresses *)
op valid_idxvals : int list -> bool.

(* Overall (generic) validity check for indices of addresses, including the number of indices *)
op valid_adrsidxs (adidxs : int list) =
  size adidxs = adrs_len /\ valid_idxvals adidxs.

(* 
  Generic validity check for the global/context part of the indices 
  corresponding to a FORS-TW address
*)
op valid_fidxvalsgp : int list -> bool.

(* Tree hash address indices validity check (local part) *)
op valid_fidxvalslptrh (adidxs : int list) : bool = 
     valid_tbidx (nth witness adidxs 1) (nth witness adidxs 0)
  /\ valid_thidx (nth witness adidxs 1)
  /\ valid_kpidx (nth witness adidxs 2)
  /\ nth witness adidxs 3 = trhtype.

(* Tree root compression address indices validity check (local part) *)
op valid_fidxvalslptrco (adidxs : int list) : bool = 
     nth witness adidxs 0 = 0
  /\ nth witness adidxs 1 = 0
  /\ valid_kpidx (nth witness adidxs 2)
  /\ nth witness adidxs 3 = trcotype.
   
(* 
  Validity check for the local part of the indices corresponding to a FORS-TW address
  (i.e., type, keypair, tree height, and tree breadth indices) 
*)
op valid_fidxvalslp (adidxs : int list) : bool =
  valid_fidxvalslptrh adidxs \/ valid_fidxvalslptrco adidxs.
  
(* 
  Overall validity check for the indices corresponding to a FORST-TW address
  (the first four indices must be valid local indices, and the remaining indices 
  must constitute valid global/context indices)
*)  
op valid_fidxvals (adidxs : int list) =
  valid_fidxvalsgp (drop 4 adidxs) /\ valid_fidxvalslp (take 4 adidxs).

(* 
  Overall validity check for the indices corresponding to a FORS-TW address,
  including the number of indices
*)    
op valid_fadrsidxs (adidxs : int list) =
  size adidxs = adrs_len /\ valid_fidxvals adidxs.

(* 
  The set of (indices corresponding to) valid FORS-TW addresses must be a subset
  of the full set of (indices corresonding to) addresses
*) 
axiom valid_fidxvals_idxvals :
  valid_fidxvals <= valid_idxvals.

(* The set of valid FORS-TW addresses is a subset of the full set of addresses *)
lemma valid_fadrsidxs_adrsidxs :
  valid_fadrsidxs <= valid_adrsidxs.
proof. 
rewrite /(<=) /valid_fadrsidxs /valid_adrsidxs => adidxs [-> /=].
by apply valid_fidxvals_idxvals.
qed.



(* - Types - *)
(* Addresses used in tweakable hash functions *)
clone import HashAddresses as HA with
  type index <= int,
    op l <- adrs_len,
    op valid_idxvals <- valid_idxvals,
    op valid_adrsidxs <- valid_adrsidxs
    
    proof ge1_l by smt(ge4_adrslen).
    
import Adrs.

type adrs = HA.adrs.

require DigitalSignatures.
print DigitalSignatures.

(* *)
module FORS_TW_ES = {
  proc keygen(ss : sseed, ps : pseed, ad : adrs) : pkFORSTW * skFORSTW =  {
    return witness;
  }
  
  proc sign(sk : skFORSTW, m : msgFORSTW) : sigFORSTW = {
    return witness;
  }
  
  proc verify(pk : pkFORSTW, m : msgFORSTW, sig : sigFORSTW) : bool = {
    return witness;
  } 
}.
