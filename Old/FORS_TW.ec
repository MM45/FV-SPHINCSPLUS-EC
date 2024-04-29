(* - Require/Import - *)
(* -- Built-In (Standard Library) -- *)
require import AllCore List Distr DList FinType IntDiv BitEncoding.
(*---*) import BS2Int BitChunking.


(* -- Local -- *)
require import BinaryTrees MerkleTrees.
require (*--*) KeyedHashFunctions TweakableHashFunctions HashAddresses.
require (*--*) DigitalSignatures.
require (*--*) OpenPRE_From_TCR_DSPR_THF.


(* - Parameters - *)
(* -- General -- *)
(* Length of addresses used in tweakable hash functions (including unspecified global/context part) *)
const adrs_len : { int | 5 <= adrs_len} as ge5_adrslen.

(* Byte-length of each private key element, public key element, and signature element *)
const n : { int | 1 <= n } as ge1_n.

(* Number of private key sets and Merkle trees *)
const k : { int | 1 <= k } as ge1_k.

(* Height of each Merkle tree *)
const a : { int | 1 <= a } as ge1_a.

(* Number of elements in each private key set and leaves in each Merkle tree *)
const t : int = 2 ^ a.

(* Address type constant for tree hashing *)
const trhtype : int.

(* Address type constant for tree root compression *)
const trcotype : int.


(* -- Instances -- *)
(* 
  Number of FORS-TW instances in a keypair set 
  (SPHINCS+: Number of leaves of single XMSS instance on bottom layer)  
*)
const l : { int | 1 <= l } as ge1_l.

(* 
  Number of keypair sets 
  (SPHINCS+: Number of XMSS instance on bottom layer)  
*)
const s : { int | 1 <= s } as ge1_s. 

(* 
  Number of FORS-TW instances to consider
  Axiomatized instead of explicitly defined to be able to instantiate.
*)
const d : { int | d = s * l } as dval.


(* -- Properties of parameters -- *)
(* The different address types are distinct *)
axiom dist_adrstypes : trhtype <> trcotype. 

(* 
  Number of leaves of a Merkle tree in a FORS-TW instance is 
  greater than or equal to 2 
*)
lemma ge2_t : 2 <= t.
proof. by rewrite /t -{1}expr1 StdOrder.IntOrder.ler_weexpn2l 2:ge1_a. qed. 

(* 
  Number of FORS-TW instances is greater than or equal to 1
*)
lemma ge1_d : 1 <= d.
proof. by rewrite dval StdOrder.IntOrder.mulr_ege1 1:ge1_s ge1_l. qed.



(* - Types (1/2) - *)
(* -- General -- *)
(* Instance index *)
clone import Subtype as InstanceIndex with
  type T <- int,
    op P i <- 0 <= i < d
    
  proof *.
  realize inhabited by exists 0; smt(ge1_d).

type iid = InstanceIndex.sT.

(* Seed for message compression key generation function *)
type mseed.

(* Randomness for non-deterministic signature generation *)
type rm.
  
(* Randomness for message compression *)
type mkey.

(* Secret seeds *)
type sseed.

(* Public seeds *)
type pseed.

(* Messages *)
type msg.


(* 
  Digests, i.e., outputs of (tweakable) hash functions. 
  In fact, also input of (tweakable) hash functions in this case.
  TODO: Probably need to assume finiteness of dgst for OpenPRE/DSPR/TCR proof.
  Perhaps make dgst a subtype of bool list where 
  P x = (exists a, a <= b /\ size x = 8 * n * a) and introduce additional parameter
  a. This would need to be propagated throughout the whole structure, so would also 
  need to adapt WOTS-TW, FL-XMSS-TW, ... :(
  
  Solution:
  Define auxiliary function for f, say fsub, that takes dgstblock as input and prove that it is
  equivalent to f as long as the input is of the right size (1 block). Then, 
  prove that the DSPR-related properties with f are equivalent to auxiliary properties that
  do use fsub instead of f. Then, prove the DSPR stuff with fsub and these auxiliary
  properties. 
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


(* -- FORS/FORS-TW specific -- *)
(* Public keys *)
type pkFORS = dgstblock.

(* Secret keys *)
clone import Subtype as DBLLKTL with
  type T <- dgstblock list list,
    op P lss <- size lss = k /\ all (fun ls => size ls = t) lss 
    
  proof *.
  realize inhabited.
    by exists (nseq k (nseq t witness)); smt(allP mem_nseq size_nseq ge1_k ge2_t). 
  qed.

type skFORS = DBLLKTL.sT.

clone import Subtype as BLKAL with
  type T <- bool list,
    op P ls <- size ls = k * a
    
  proof *.
  realize inhabited by exists (nseq (k * a) witness); smt(size_nseq ge1_k ge1_a).

type msgFORSTW = BLKAL.sT.

(* Lists of length a containing digests with length 1 (block of 8 * n bits) *)
clone import Subtype as DBAL with
  type T   <- dgstblock list,
    op P ls <- size ls = a
    
  proof *.
  realize inhabited by exists (nseq a witness); smt(size_nseq ge1_a).
   
(* Authentication paths in Merkle trees *)
type apFORSTW = DBAL.sT.

(* Lists of length k containing skFORSTW (single element)/apFORSTW pairs *)
clone import Subtype as DBAPKL with
  type T   <- (dgstblock * apFORSTW) list,
    op P ls <- size ls = k
    
  proof *.
  realize inhabited by exists (nseq k witness); smt(size_nseq ge1_k).

(* Signatures *)
type sigFORSTW = DBAPKL.sT.



(* - Operators (1/2) - *)
(* -- Auxiliary -- *)
(* Number of nodes in a Merkle tree (of total height a) at a particular height a' *)
op nr_nodes (a' : int) = 2 ^ (a - a').


(* -- Validity checks -- *)
(* Tree (keypair set) index validity check *)
op valid_tidx (tidx : int) : bool =
  0 <= tidx < s.

(*
(* Type index validity check *)
op valid_typeidx (typeidx : int) : bool =
  typeidx = trhtype \/ typeidx = trcotype.
*)

(* Keypair index validity check *)
op valid_kpidx (kpidx : int) : bool = 
  0 <= kpidx < l.

(* Tree height index validity check *)
op valid_thidx (thidx : int) : bool = 
  0 <= thidx <= a.

(* 
  Tree breadth index validity check.
  Note that, according to the specs, this index is not reset
  across Merkle trees in a FORS-TW instance. E.g.,
  the breadth index of the left-most leaf of the i-th tree (out of k)
  has breadth index i * t; the left-most node of the i-th tree at
  height 1 has breadth index i * (t // 2); and the root node of the
  i-th tree has breadth index i. In other words, the left-most node of 
  a certain layer in the i-th tree is given the incremented breadth index
  from the right-most node at the same layer of the (i - 1)-th tree.
  The generic formula for the breadth index of a node at height j in the
  i-th tree should thus be i * (t // 2 ^ j).
*)
op valid_tbidx (thidx tbidx : int) : bool =
  0 <= tbidx < k * nr_nodes thidx.

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
  /\ nth witness adidxs 3 = trhtype
  /\ valid_tidx (nth witness adidxs 4).
  
(* Tree root compression address indices validity check (local part) *)
op valid_fidxvalslptrco (adidxs : int list) : bool = 
     nth witness adidxs 0 = 0
  /\ nth witness adidxs 1 = 0
  /\ valid_kpidx (nth witness adidxs 2)
  /\ nth witness adidxs 3 = trcotype
  /\ valid_tidx (nth witness adidxs 4).
   
(* 
  Validity check for the local part of the indices corresponding to a FORS-TW address
  (i.e., type, keypair, tree height, and tree breadth indices) 
*)
op valid_fidxvalslp (adidxs : int list) : bool =
  valid_fidxvalslptrh adidxs \/ valid_fidxvalslptrco adidxs.
  
(* 
  Overall validity check for the indices corresponding to a FORS-TW address
  (the first four indices must be valid local indices, and the remaining indices 
  must constitute valid global/context indices)
*)  
op valid_fidxvals (adidxs : int list) =
  valid_fidxvalsgp (drop 5 adidxs) /\ valid_fidxvalslp (take 5 adidxs).

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

(* 
  The set of (indices corresponding to) valid FORS-TW addresses must be a subset
  of the full set of (indices corresonding to) addresses, including length check
*) 
lemma valid_fadrsidxs_adrsidxs :
  valid_fadrsidxs <= valid_adrsidxs.
proof. 
rewrite /(<=) /valid_fadrsidxs /valid_adrsidxs => adidxs [-> /=].
by apply valid_fidxvals_idxvals.
qed.



(* - Distributions - *)  
(* Proper distribution over seeds for message compression key generation function *)
op [lossless] dmseed : mseed distr.

(* Proper distribution over randomness for non-deterministic signature generation *)
op [lossless] drm : rm distr.

(* Proper distribution over randomness for message compression *)
op [lossless] dmkey : mkey distr.

(* Proper distribution over public seeds *)
op [lossless] dpseed : pseed distr.

(* Proper distribution over secret seeds *)
op [lossless] dsseed : sseed distr.

(* Proper distribution over digests of length 1 (block of 8 * n bits) *)
op [lossless] ddgstblock : dgstblock distr.

(* Proper distribution over digests of length 1 (block of 8 * n bits), lifted to dgst type *)
op ddgstblocklift : dgst distr = dmap ddgstblock DigestBlock.val.

lemma ddgstblocklift_ll : is_lossless ddgstblocklift.
proof. by rewrite dmap_ll ddgstblock_ll. qed.


(* 
  Proper distribution that samples a length t list of dgstblock elements by
  independently sampling each element from ddgstblock
*)
op ddgstblockt : dgstblock list distr = dlist ddgstblock t.

op dskFORS : skFORS distr = dmap (dlist ddgstblockt k) DBLLKTL.insubd.

lemma dskFORS_ll : is_lossless dskFORS.
proof. by rewrite dmap_ll 2!dlist_ll ddgstblock_ll. qed.


(* - Types (2/2) - *)
(* -- General -- *)
(* Addresses used in tweakable hash functions *)
clone import HashAddresses as HA with
  type index <= int,
    op l <- adrs_len,
    op valid_idxvals <- valid_idxvals,
    op valid_adrsidxs <- valid_adrsidxs
    
    proof ge1_l by smt(ge5_adrslen).
    
import Adrs.


(* -- FORS/FORS-TW specific -- *)
(* Public keys *)
type pkFORSTW = pkFORS * pseed * adrs.

(* Secret keys *)
type skFORSTW = sseed * pseed * adrs.



(* - Operators (2/2) - *)
(* -- Validity checks -- *)
(* Overall (generic) validity check for addresses *)
op valid_adrs (ad : adrs) =
  valid_adrsidxs (val ad).

(* Overall validity check for FORS-TW addresses *)    
op valid_fadrs (ad : adrs) : bool =
  valid_fadrsidxs (val ad).

(* The set of valid FORS-TW addresses is a subset of the full set of addresses *)
lemma valid_fadrs_adrs :
  valid_fadrs <= valid_adrs.
proof. smt(valid_fadrsidxs_adrsidxs). qed.


(* -- Setters -- *)
op set_tidx (ad : adrs) (i : int) : adrs =
  set_idx ad 4 i.
  
op set_typeidx (ad : adrs) (i : int) : adrs =
  insubd (put (put (put (put (val ad) 0 0) 1 0) 2 0) 3 i).

op set_kpidx (ad : adrs) (i : int) : adrs =
  set_idx ad 2 i.
  
op set_thtbidx (ad : adrs) (i j : int) : adrs =
  insubd (put (put (val ad) 0 j) 1 i).


(* -- Getters -- *)
op get_kpidx (ad : adrs) : int =
  get_idx ad 2.
  

(* -- Keyed Hash Functions -- *)
(* Secret key element generation function *)
op skg : sseed -> (pseed * adrs) -> dgstblock.

clone KeyedHashFunctions as SKG with
  type key_t <- sseed,
  type in_t <- pseed * adrs,
  type out_t <- dgstblock,
  
    op f <- skg
    
  proof *.

clone import SKG.PRF as SKG_PRF with
  op dkey <- dsseed,
  op doutm d <- ddgstblock
  
  proof *.
  realize dkey_ll by exact: dsseed_ll.
  realize doutm_ll by move => d; apply ddgstblock_ll. 
  

(* --- Message compression --- *)
(* Message compression key geneneration function *)
op mkg : mseed -> (rm * msg) -> mkey.

clone KeyedHashFunctions as MKG with
  type key_t <- mseed,
  type in_t <- rm * msg,
  type out_t <- mkey,
  
    op f <- mkg
    
  proof *.

clone import MKG.PRF as MKG_PRF with
    op dkey <- dmseed,
    op doutm x <- dmkey 
  
  proof *.
  realize dkey_ll by exact: dmseed_ll.
  realize doutm_ll by move=> ?; apply dmkey_ll.
  
(* Message compression function *)
op mco : mkey -> msg -> msgFORSTW * iid.

(* 
  Function mapping output of message compression function to a list
  containing three-tuples of which the entries respectively signify the following.
  - The index of a key set (i.e., pointer to a specific FORS-TW instance).
  - The index of a secret value set (i.e., pointer to Merkle tree in FORS-TW instance indicated by first value of tuple). 
  - The index of a secret value (i.e., pointer to a leaf of the Merkle tree indicated by second value of tuple). 
*)
op g (mi : msgFORSTW * iid) : (int * int * int) list =
  let cmsg = chunk a (val mi.`1) in
  let iidx = val mi.`2 in
    mkseq (fun (i : int) => (iidx, i, bs2int (rev (nth witness cmsg i)))) k.

clone KeyedHashFunctions as MCO with
  type key_t <- mkey,
  type in_t <- msg,
  type out_t <- msgFORSTW * iid,
  
    op f <- mco
    
  proof *.
  
clone import MCO.ITSR as MCO_ITSR with  
  op ks <- d,
  op svsks <- k,
  op svsvs <- t,
  
  op g <- g,
  
  op dkey <- dmkey
  
  proof *.
  realize ge1_ks by exact: ge1_d.
  realize ge1_svsks by exact: ge1_k.
  realize ge1_svsvs by smt(ge2_t).
  realize size_g by move=> mi @/g /=; rewrite size_mkseq; smt(ge1_k).
  realize rng_iks. by move => x mi @/g /= /mkseqP [i] [_ ->] /=; rewrite valP. qed.
  realize rng_sv.
    move=> x mi @/g /= /mkseqP [i] [rng_i -> /=].
    rewrite bs2int_ge0 /= /t; pose r := rev _.
    suff ->: a = size r; 1: by rewrite bs2int_le2Xs.
    rewrite /r size_rev. search size nth.
    have: all (((=) a) \o size) (chunk a (val mi.`1)).
    + rewrite allP => bs bsin.
      by rewrite /(\o) eq_sym (in_chunk_size a (val mi.`1)) //; smt(ge1_a).
    move/all_nthP => /= /(_ witness i _) //.
    by rewrite size_chunk 2:valP 2:mulzK; smt(ge1_a).
  qed.
  realize eqiks_g. by move=> x x' mi @/g /= /mkseqP [?] [? ->] /mkseqP [?] [? ->]. qed.
  realize neqisvs_g. 
    move=> x x' mi @/g /= /mkseqP [i] [rng_i ->] /mkseqP [j] [rng_j ->] /=. 
    by apply contra => ->.
  qed.
  realize dkey_ll by exact: dmkey_ll.


(* -- Tweakable Hash Functions -- *)
(* 
  Tweakable hash function collection that contains all tweakable hash functions
  used in FORS-TW, SPHINCS+ 
*)
op thfc : int -> pseed -> adrs -> dgst -> dgstblock.


(* 
  Tweakable hash function used to produce leaves from secret key values.
  (Same function as used in chains for WOTS-TW)

op f : pseed -> adrs -> dgst -> dgstblock.
*)
op f : pseed -> adrs -> dgst -> dgstblock = thfc (8 * n).

clone TweakableHashFunctions as F with
  type pp_t <- pseed,
  type tw_t <- adrs,
  type in_t <- dgst,
  type out_t <- dgstblock,
  
    op f <- f,
  
    op dpp <- dpseed
    
  proof *.
  realize dpp_ll by exact: dpseed_ll.

(*
clone import F.SMDTTCR as F_TCR with
  op t_smdttcr <- d * k * t
  
  proof *.
  realize ge0_tsmdttcr by smt(ge1_d ge1_k ge2_t).
*)

clone import F.Collection as FC with
  type diff_t <- int,
  
    op get_diff <- size,
    
    op fc <- thfc
    
  proof *.
  realize in_collection by exists (8 * n).

clone import FC.SMDTOpenPREC as FC_OpenPRE with
  op t_smdtopenpre <- d * k * t,
  
  op din <- ddgstblocklift
    
  proof *.
  realize ge0_tsmdtopenpre by smt(ge1_d ge1_k ge2_t).
  realize din_ll by exact: ddgstblocklift_ll.
    
clone import FC.SMDTTCRC as FC_TCR with
  op t_smdttcr <- d * k * t
  
  proof *.
  realize ge0_tsmdttcr by smt(ge1_d ge1_k ge2_t).

(* Tweakable hash function used to construct Merkle trees from leaves
op trh : pseed -> adrs -> dgst -> dgstblock.
*)
op trh : pseed -> adrs -> dgst -> dgstblock = thfc (8 * n * 2).

clone import TweakableHashFunctions as TRH with
  type pp_t <- pseed,
  type tw_t <- adrs,
  type in_t <- dgst,
  type out_t <- dgstblock,
  
    op f <- trh,
  
    op dpp <- dpseed
    
  proof *.
  realize dpp_ll by exact: dpseed_ll.

(*
clone import TRH.SMDTTCR as TRH_TCR with
  op t_smdttcr <- d * k * (t - 1)
  
  proof *.
  realize ge0_tsmdttcr by smt(ge1_d ge1_k ge2_t).
*)

clone import TRH.Collection as TRHC with
  type diff_t <- int,
  
    op get_diff <- size,
    
    op fc <- thfc
    
  proof *.
  realize in_collection by exists (8 * n * 2).

clone import TRHC.SMDTTCRC as TRHC_TCR with
  op t_smdttcr <- d * k * (t - 1)
  
  proof *.
  realize ge0_tsmdttcr by smt(ge1_d ge1_k ge2_t).

(* Tweakable hash function used compress Merkle tree roots to public key
op trco : pseed -> adrs -> dgst -> dgstblock.
*)
op trco : pseed -> adrs -> dgst -> dgstblock = thfc (8 * n * k).

clone TweakableHashFunctions as TRCO with
  type pp_t <- pseed,
  type tw_t <- adrs,
  type in_t <- dgst,
  type out_t <- dgstblock,
  
    op f <- trco,
  
    op dpp <- dpseed
    
  proof *.
  realize dpp_ll by exact: dpseed_ll.
(*
clone import TRCO.SMDTTCR as TRCO_TCR with
  op t_smdttcr <- d * k
  
  proof *.
  realize ge0_tsmdttcr by smt(ge1_d ge1_k).
*)
  
clone import TRCO.Collection as TRCOC with
  type diff_t <- int,
  
    op get_diff <- size,
    
    op fc <- thfc
    
  proof *.
  realize in_collection by exists (8 * n * k).

clone import TRCOC.SMDTTCRC as TRCOC_TCR with
  op t_smdttcr <- d * k
  
  proof *.
  realize ge0_tsmdttcr by smt(ge1_d ge1_k).


(* -- Merkle trees -- *)
(* Update function for height and breadth indices (down the tree) *)
op updhbidx (hbidx : int * int) (b : bool) : int * int = 
  (hbidx.`1 - 1, if b then 2 * hbidx.`2 + 1 else 2 * hbidx.`2).

(* Function around trh with desired form for use in abstract merkle tree operators  *)
op trhi (ps : pseed) (ad : adrs) (hbidx : int * int) (x x' : dgstblock) : dgstblock =
  trh ps (set_thtbidx ad hbidx.`1 hbidx.`2) (val x ++ val x').
  
(*
(* 
  Computes the (hash) value corresponding to the root of the binary tree w.r.t.
  a certain public seed, address, height index, and breadth index. 
*)
op val_bt_trh (bt : dgstblock bintree) (ps : pseed) (ad : adrs) (hidx : int) (bidx : int) : dgstblock =
  with bt = Leaf x => x
  with bt = Node l r => 
    trh ps (set_thtbidx ad hidx bidx) 
        (val (val_bt_trh l ps ad (hidx - 1) (2 * bidx)) ++ val (val_bt_trh r ps ad (hidx - 1) (2 * bidx + 1))).
*)
op val_bt_trh_gen (ps : pseed) (ad : adrs) (bt : dgstblock bintree) (hidx bidx : int) : dgstblock =
  val_bt (trhi ps ad) updhbidx bt (hidx, bidx).

op val_bt_trh (ps : pseed) (ad : adrs) (bt : dgstblock bintree) (bidx : int) : dgstblock =
  val_bt_trh_gen ps ad bt a bidx.
  
(*     
(* 
  Constructs an authentication path (without embedding it in the corresponding subtype)
  from a binary tree and a path represented by a boolean list w.r.t. a certain 
  public seed, address, height index, and breadth index. 
*)
op cons_ap_trh_gen (bt : dgstblock bintree) (bs : bool list) (ps : pseed) (ad : adrs) (hidx : int) (bidx : int) : dgstblock list =
  with bt = Leaf _, bs = [] => []
  with bt = Leaf _, bs = _ :: _ => witness
  with bt = Node _ _, bs = [] => witness
  with bt = Node l r, bs = b :: bs' =>
    (val_bt_trh (if b then l else r) ps ad (hidx - 1) (if b then 2 * bidx else 2 * bidx + 1)) 
     :: cons_ap_trh_gen (if b then r else l) bs' ps ad (hidx - 1) (if b then 2 * bidx + 1 else 2 * bidx). 
*)
op cons_ap_trh_gen (ps : pseed) (ad : adrs) (bt : dgstblock bintree) (bs : bool list) (hidx bidx : int) : dgstblock list =
  cons_ap (trhi ps ad) updhbidx bt bs (hidx, bidx).


(*
(* 
  Constructs authentication path (embedding it in the corresponding subtype)
  for the special case of binary trees of height a w.r.t. a certain public seed, address, 
  height index a, and breadth index bidx. Here, idx should be a valid leaf index (i.e., in [0, 2 ^ a -1])
  and bidx should be a valid breadth index for root nodes of the Merkle trees in a FORS-TW 
  instance (i.e., in [0, k - 1]).
*)
op cons_ap_trh (bt : dgstblock bintree) (idx : int) (ps : pseed) (ad : adrs) (bidx : int) : apFORSTW =
  DBAL.insubd (cons_ap_trh_gen bt (rev (int2bs a idx)) ps ad a bidx).
*)
op cons_ap_trh (ps : pseed) (ad : adrs) (bt : dgstblock bintree) (idx : int) (bidx : int) : apFORSTW =
  DBAL.insubd (cons_ap_trh_gen ps ad bt (rev (int2bs a idx)) a bidx).

  
(*
(*
  Computes the (hash) value corresponding to an authentication path, a leaf, and a 
  path represented by a boolean list w.r.t a certain public seed, address, height index, 
  and breadth index.
*)        
op val_ap_trh_gen (ap : dgstblock list) (bs : bool list) (leaf : dgstblock) (ps : pseed) (ad : adrs) (hidx : int) (bidx : int) : dgstblock =
  with ap = [], bs = [] => leaf
  with ap = [], bs = _ :: _ => witness 
  with ap = _ :: _, bs = [] => witness
  with ap = x :: ap', bs = b :: bs' =>
    trh ps (set_thtbidx ad hidx bidx) 
        (if b 
         then val x ++ val (val_ap_trh_gen ap' bs' leaf ps ad (hidx - 1) (2 * bidx + 1))
         else val (val_ap_trh_gen ap' bs' leaf ps ad (hidx - 1) (2 * bidx)) ++ val x).
*)
op val_ap_trh_gen (ps : pseed) (ad : adrs) (ap : dgstblock list) (bs : bool list) (leaf : dgstblock) (hidx bidx : int) : dgstblock =
  val_ap (trhi ps ad) updhbidx ap bs leaf (hidx, bidx).

(*
(* 
  Computes value corresponding to an authentication path, leaf, and a path represented 
  by the big-endian binary representation of an index  w.r.t. a certain public seed, address, 
  height index a, and breadth index bidx. Here, idx should be a valid leaf index (i.e., in [0, 2 ^ a -1])
  and bidx should be a valid breadth index for root nodes of the Merkle trees in a FORS-TW 
  instance (i.e., in [0, k - 1]).
*)
op val_ap_trh (ap : apFORSTW) (idx : int) (leaf : dgstblock) (ps : pseed) (ad : adrs) (bidx : int) : dgstblock = 
  val_ap_trh_gen (val ap) (rev (int2bs a idx)) leaf ps ad a bidx.
*)

op val_ap_trh (ps : pseed) (ad : adrs) (ap : apFORSTW) (idx : int) (leaf : dgstblock) (bidx : int) : dgstblock =
  val_ap_trh_gen ps ad (val ap) (rev (int2bs a idx)) leaf a bidx. 

(* 
  Extracts collision from original binary tree (bt) and 
  an authentication path/leaf (ap, bs, leaf), if any. 
*)
op extract_collision_bt_ap_trh (ps : pseed) 
                               (ad : adrs) 
                               (bt : dgstblock bintree) 
                               (ap : dgstblock list) 
                               (bs : bool list) 
                               (leaf : dgstblock) 
                               (bidx : int) =
  extract_collision_bt_ap (trhi ps ad) updhbidx bt ap bs leaf (a, bidx).



(* - Specifications - *)
(* -- With PRF -- *)
(* 
  Fixed-Length FORS-TW in Encompassing Structure.
  Auxiliary scheme to simplify specification of multi-instance FORS-TW scheme.
  Represents single FORS-TW instance that signs fixed-length messages. 
*)
module FL_FORS_TW_ES = {
  proc gen_leaves_single_tree(idxt : int, ss : sseed, ps : pseed, ad : adrs) : dgstblock list = {
    var skFORS_ele : dgstblock;
    var leaf : dgstblock;
    var leaves : dgstblock list;
    
    leaves <- [];
    while (size leaves < t) {
      skFORS_ele <- skg ss (ps, set_thtbidx ad 0 (idxt * t + size leaves));
      leaf <- f ps (set_thtbidx ad 0 (idxt * t + size leaves)) (val skFORS_ele);
      leaves <- rcons leaves leaf;
    }
    
    return leaves;
  }
  
  proc gen_pkFORS(ss : sseed, ps : pseed, ad : adrs) : pkFORS = {
    var pkFORS : dgstblock;
    var leaves : dgstblock list;
    var root : dgstblock;
    var roots : dgstblock list;
    var kpidx : int;
    
    roots <- [];
    while (size roots < k) {
      leaves <@ gen_leaves_single_tree(size roots, ss, ps, ad); 
      root <- val_bt_trh ps ad (list2tree leaves) (size roots);
      roots <- rcons roots root;
    }
     
    pkFORS <- trco ps (set_kpidx (set_typeidx ad trcotype) (get_kpidx ad)) (flatten (map DigestBlock.val roots));
    
    return pkFORS;  
  }
  
  proc keygen(ss : sseed, ps : pseed, ad : adrs) : pkFORSTW * skFORSTW =  {
    var pkFORS : pkFORS;
    var pk : pkFORSTW;
    var sk : skFORSTW;
    
    pkFORS <@ gen_pkFORS(ss, ps, ad);
    
    pk <- (pkFORS, ps, ad);
    sk <- (ss, ps, ad);
    
    return (pk, sk);
  }
  
  proc sign(sk : skFORSTW, m : msgFORSTW) : sigFORSTW = {
    var ss : sseed;
    var ps : pseed;
    var ad : adrs;
    var bsidx : bool list;
    var idx : int;
    var skFORS_ele : dgstblock;
    var leaves : dgstblock list;
    var ap : apFORSTW;
    var sig : (dgstblock * apFORSTW) list;
    
    (ss, ps, ad) <- sk;
    
    sig <- [];
    while (size sig < k) {
      bsidx <- take a (drop (a * (size sig)) (val m));  
      idx <- bs2int (rev bsidx);
      skFORS_ele <- skg ss (ps, set_thtbidx ad 0 (size sig * t + idx));
      leaves <@ gen_leaves_single_tree(size sig, ss, ps, ad);
      ap <- cons_ap_trh ps ad (list2tree leaves) idx (size sig);
      sig <- rcons sig (skFORS_ele, ap);
    }
    
    return insubd sig;
  }
  
  proc pkFORS_from_sigFORSTW(sig : sigFORSTW, m : msgFORSTW, ps : pseed, ad : adrs) : pkFORS = {
    var skFORS_ele : dgstblock;
    var ap : apFORSTW;
    var leaf : dgstblock;
    var bsidx : bool list;
    var idx : int;
    var roots : dgstblock list;
    var root : dgstblock;
    var pkFORS : pkFORS;
    
    roots <- [];
    while (size roots < k) {
      bsidx <- take a (drop (a * (size roots)) (val m));  
      idx <- bs2int (rev bsidx);
      (skFORS_ele, ap) <- nth witness (val sig) (size roots);
      leaf <- f ps (set_thtbidx ad 0 (size roots * t + idx)) (val skFORS_ele);
      root <- val_ap_trh ps ad ap idx leaf (size roots);
      roots <- rcons roots root;
    }
    
    pkFORS <- trco ps (set_kpidx (set_typeidx ad trcotype) (get_kpidx ad)) (flatten (map DigestBlock.val roots));
    
    return pkFORS;
  }
  
  proc verify(pk : pkFORSTW, m : msgFORSTW, sig : sigFORSTW) : bool = {
    var ps : pseed;
    var ad : adrs;
    var pkFORS, pkFORS' : pkFORS;
    
    (pkFORS, ps, ad) <- pk;
    
    pkFORS' <@ pkFORS_from_sigFORSTW(sig, m, ps, ad);
    
    return pkFORS' = pkFORS;
  } 
}.

(* 
  Multi-instance FORS-TW in Encompassing Structure.
*)
module M_FORS_TW_ES = {
  proc gen_pkFORSs (ss : sseed, ps : pseed, ad : adrs) : pkFORS list list = {
    var pkFORS : pkFORS;
    var pkFORSl : pkFORS list;
    var pkFORSs : pkFORS list list;
     
    (* 
      Total of d instances, but these are divided in 
      s sets (SPHINCS+: XMSS instances on bottom layer) 
      each containing l instances (SPHINCS+: leaves of XMSS instance on bottom layer)
    *)
    pkFORSs <- [];
    while (size pkFORSs < s) {
      pkFORSl <- [];
      while (size pkFORSl < l) {
        pkFORS <@ FL_FORS_TW_ES.gen_pkFORS(ss, ps, set_kpidx (set_tidx ad (size pkFORSs)) (size pkFORSl));
        pkFORSl <- rcons pkFORSl pkFORS; 
      }
      
      pkFORSs <- rcons pkFORSs pkFORSl;
    }
    
    return pkFORSs;
  }
   
  proc keygen(ss : sseed, ps : pseed, ad : adrs) : (pkFORS list list * pseed * adrs) * (mseed * sseed * pseed * adrs) =  {
    var ms : mseed;
    var pkFORSs : pkFORS list list;
    var pk : (pkFORS list list * pseed * adrs);
    var sk : mseed * sseed * pseed * adrs;
    
    ms <$ dmseed;
    
    pkFORSs <@ gen_pkFORSs(ss, ps, set_typeidx ad trhtype);
    
    pk <- (pkFORSs, ps, ad);
    sk <- (ms, ss, ps, ad);
    
    return (pk, sk);
  }
  
  proc sign(sk : mseed * sseed * pseed * adrs, m : msg) : mkey * sigFORSTW = {
    var ms : mseed;
    var ss : sseed;
    var ps : pseed;
    var ad : adrs;
    var r : rm; 
    var mk : mkey;
    var cm : msgFORSTW;
    var idx : iid;
    var tidx, kpidx : int;
    var sig : sigFORSTW;
    
    (ms, ss, ps, ad) <- sk;
    
    r <$ drm;
    
    mk <- mkg ms (r, m);
    
    (cm, idx) <- mco mk m;
    
    (tidx, kpidx) <- edivz (val idx) l;
    
    sig <@ FL_FORS_TW_ES.sign((ss, ps, set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx), cm);
    
    return (mk, sig);
  }
  
  proc verify(pk : pkFORS list list * pseed * adrs, m : msg, sig : mkey * sigFORSTW) : bool = {
    var pkFORS : pkFORS;
    var pkFORSl : pkFORS list list;
    var ps : pseed;
    var ad : adrs;
    var mk : mkey;
    var sigFORSTW : sigFORSTW;
    var cm : msgFORSTW;
    var idx : iid;
    var tidx, kpidx : int;
    var is_valid : bool; 
        
    (pkFORSl, ps, ad) <- pk;
    (mk, sigFORSTW) <- sig;
    
    (cm, idx) <- mco mk m;
    
    (tidx, kpidx) <- edivz (val idx) l;
    
    pkFORS <- nth witness (nth witness pkFORSl tidx) kpidx;
    
    is_valid <@ FL_FORS_TW_ES.verify((pkFORS, ps, set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx), cm, sigFORSTW);
    
    return is_valid;
  } 
}.


(* -- Without PRF -- *)
(* 
  Fixed-Length FORS-TW in Encompassing Structure (No PRF).
  Auxiliary scheme to simplify specification of multi-instance FORS-TW scheme.
  Represents single FORS-TW instance that signs fixed-length messages. 
*)
module FL_FORS_TW_ES_NPRF = {
  proc gen_leaves_single_tree(idxt : int, skFORS : skFORS, ps : pseed, ad : adrs) : dgstblock list = {
    var skFORS_ele : dgstblock;
    var leaf : dgstblock;
    var leaves : dgstblock list;
    
    leaves <- [];
    while (size leaves < t) {
      skFORS_ele <- nth witness (nth witness (val skFORS) idxt) (size leaves);
      leaf <- f ps (set_thtbidx ad 0 (idxt * t + size leaves)) (val skFORS_ele);
      leaves <- rcons leaves leaf;
    }
    
    return leaves;
  }
  
  proc gen_pkFORS(skFORS : skFORS, ps : pseed, ad : adrs) : pkFORS = {
    var pkFORS : dgstblock;
    var leaves : dgstblock list;
    var root : dgstblock;
    var roots : dgstblock list;
    
    roots <- [];
    while (size roots < k) {
      leaves <@ gen_leaves_single_tree(size roots, skFORS, ps, ad); 
      root <- val_bt_trh ps ad (list2tree leaves) (size roots);
      roots <- rcons roots root;
    }
     
    pkFORS <- trco ps (set_kpidx (set_typeidx ad trcotype) (get_kpidx ad)) (flatten (map DigestBlock.val roots));
    
    return pkFORS;
  }
  
  proc keygen(ps : pseed, ad : adrs) : pkFORSTW * (skFORS * pseed * adrs) =  {
    var pkFORS : pkFORS;
    var skFORS : skFORS;
    var pk : pkFORSTW;
    var sk : skFORS * pseed * adrs;
    
    skFORS <$ dskFORS;
    
    pkFORS <@ gen_pkFORS(skFORS, ps, ad);
    
    pk <- (pkFORS, ps, ad);
    sk <- (skFORS, ps, ad);
    
    return (pk, sk);
  }
  
  proc sign(sk : skFORS * pseed * adrs, m : msgFORSTW) : sigFORSTW = {
    var skFORS : skFORS;
    var ps : pseed;
    var ad : adrs;
    var bsidx : bool list;
    var idx : int;
    var skFORS_ele : dgstblock;
    var leaves : dgstblock list;
    var ap : apFORSTW;
    var sig : (dgstblock * apFORSTW) list;
    
    (skFORS, ps, ad) <- sk;
    
    sig <- [];
    while (size sig < k) {
      bsidx <- take a (drop (a * (size sig)) (val m));  
      idx <- bs2int (rev bsidx);
      skFORS_ele <- nth witness (nth witness (val skFORS) (size sig)) idx;
      leaves <@ gen_leaves_single_tree(size sig, skFORS, ps, ad);
      ap <- cons_ap_trh ps ad (list2tree leaves) idx (size sig);
      sig <- rcons sig (skFORS_ele, ap);
    }
    
    return insubd sig;
  }
  
  proc pkFORS_from_sigFORSTW(sig : sigFORSTW, m : msgFORSTW, ps : pseed, ad : adrs) : pkFORS = {
    var skFORS_ele : dgstblock;
    var ap : apFORSTW;
    var leaf : dgstblock;
    var bsidx : bool list;
    var idx : int;
    var roots : dgstblock list;
    var root : dgstblock;
    var pkFORS : pkFORS;
    
    roots <- [];
    while (size roots < k) {
      bsidx <- take a (drop (a * (size roots)) (val m));  
      idx <- bs2int (rev bsidx);
      (skFORS_ele, ap) <- nth witness (val sig) (size roots);
      leaf <- f ps (set_thtbidx ad 0 (size roots * t + idx)) (val skFORS_ele);
      root <- val_ap_trh ps ad ap idx leaf (size roots);
      roots <- rcons roots root;
    }
    
    pkFORS <- trco ps (set_kpidx (set_typeidx ad trcotype) (get_kpidx ad)) (flatten (map DigestBlock.val roots));
    
    return pkFORS;
  }
  
  proc verify(pk : pkFORSTW, m : msgFORSTW, sig : sigFORSTW) : bool = {
    var ps : pseed;
    var ad : adrs;
    var pkFORS, pkFORS' : pkFORS;
    
    (pkFORS, ps, ad) <- pk;
    
    pkFORS' <@ pkFORS_from_sigFORSTW(sig, m, ps, ad);
    
    return pkFORS' = pkFORS;
  } 
}.

(* 
  Multi-instance FORS-TW in Encompassing Structure (No PRF).
*)
module M_FORS_TW_ES_NPRF = {
  proc keygen(ps : pseed, ad : adrs) : (pkFORS list list * pseed * adrs) * (skFORS list list * pseed * adrs) =  {
    (*
    var ps : pseed;
    var ad : adrs;
    *)
    var skFORS : skFORS;
    var pkFORS : pkFORS;
    var pkFORSl : pkFORS list;
    var skFORSl : skFORS list;
    var skFORSs : skFORS list list;
    var pkFORSs : pkFORS list list;
    var pk : (pkFORS list list * pseed * adrs);
    var sk : (skFORS list list * pseed * adrs);
    
    (*
    ps <$ dpseed;
    ad <- witness;
    *)
    
    (* 
      Total of d instances, but these are divided in 
      s sets (SPHINCS+: XMSS instances on bottom layer) 
      each containing l instances (SPHINCS+: leaves of XMSS instance on bottom layer)
    *)
    skFORSs <- [];
    pkFORSs <- [];
    while (size skFORSs < s) {
      skFORSl <- [];
      pkFORSl <- [];
      while (size skFORSl < l) {
        skFORS <$ dskFORS;
        pkFORS <@ FL_FORS_TW_ES_NPRF.gen_pkFORS(skFORS, ps, set_kpidx (set_tidx ad (size skFORSs)) (size skFORSl));
        skFORSl <- rcons skFORSl skFORS;
        pkFORSl <- rcons pkFORSl pkFORS; 
      }
      
      skFORSs <- rcons skFORSs skFORSl;
      pkFORSs <- rcons pkFORSs pkFORSl;
    }
        
    pk <- (pkFORSs, ps, ad);
    sk <- (skFORSs, ps, ad);
    
    return (pk, sk);
  }
  
  proc sign(sk : skFORS list list * pseed * adrs, m : msg) : mkey * sigFORSTW = {
    var skFORS : skFORS;
    var skFORSs : skFORS list list;
    var ps : pseed;
    var ad : adrs;
    var mk : mkey;
    var cm : msgFORSTW;
    var idx : iid;
    var tidx, kpidx : int;
    var sig : sigFORSTW;
    
    (skFORSs, ps, ad) <- sk;
    
    mk <$ dmkey;
    
    (cm, idx) <- mco mk m;
    
    (tidx, kpidx) <- edivz (val idx) l;
    
    skFORS <- nth witness (nth witness skFORSs tidx) kpidx;
     
    sig <@ FL_FORS_TW_ES_NPRF.sign((skFORS, ps, set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx), cm);
    
    return (mk, sig);
  }
  
  proc verify(pk : pkFORS list list * pseed * adrs, m : msg, sig : mkey * sigFORSTW) : bool = {
    var pkFORS : pkFORS;
    var pkFORSs : pkFORS list list;
    var ps : pseed;
    var ad : adrs;
    var mk : mkey;
    var sigFORSTW : sigFORSTW;
    var cm : msgFORSTW;
    var idx : iid;
    var tidx, kpidx : int;
    var is_valid : bool; 
        
    (pkFORSs, ps, ad) <- pk;
    (mk, sigFORSTW) <- sig;
    
    (cm, idx) <- mco mk m;
    
    (tidx, kpidx) <- edivz (val idx) l;
    
    pkFORS <- nth witness (nth witness pkFORSs tidx) kpidx;
    
    is_valid <@ FL_FORS_TW_ES_NPRF.verify((pkFORS, ps, set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx), cm, sigFORSTW);
    
    return is_valid;
  } 
}.




(* - Proof - *)
(*
(* -- Import of relevant definitions and properties --  *)
clone import DigitalSignatures as DSS_MFORSTWESNPRF with
  type pk_t <- pkFORS list list * pseed * adrs,
  type sk_t <- skFORS list list * pseed * adrs,
  type msg_t <- msg,
  type sig_t <- mkey * sigFORSTW
  
  proof *.

import Stateless.
*)

(* -- Oracle interfaces -- *)
(*
module O_CMA_MFORSTWESNPRF = O_CMA_Default(M_FORS_TW_ES_NPRF).

module O_CMA_MFORSTWESNPRF_AV = {
  include var O_CMA_MFORSTWESNPRF [-init, sign] 
  
  var lidxs : (int * int * int) list
  
  proc init(sk_init : skFORS list list * pseed * adrs) : unit = {
    O_CMA_MFORSTWESNPRF.init(sk);
    lidxs <- [];
  }
  
  proc sign(m : msg) : mkey * sigFORSTW = {
    var mk : mkey;
    var sigFORSTW : sigFORSTW;
    
    (mk, sigFORSTW) <@ O_CMA_MFORSTWESNPRF.sign(m);
    
    lidxs <- lidxs ++ g (mco mk m);
    
    return (mk, sigFORSTW);  
  }
}. 
*)
module type Oracle_CMA_MFORSTWESNPRF = {
  proc init(sk_init : skFORS list list * pseed * adrs) : unit
  proc sign(m : msg) : mkey * sigFORSTW
  proc fresh(m : msg) : bool
  proc nr_queries() : int
}.

module type SOracle_CMA_MFORSTWESNPRF = {
  include Oracle_CMA_MFORSTWESNPRF [sign]
}.



(* -- Adversary classes -- *)
module type Adv_EUFCMA_MFORSTWESNPRF (O : SOracle_CMA_MFORSTWESNPRF) = {
  proc forge(pk : pkFORS list list * pseed * adrs) : msg * (mkey * sigFORSTW)
}.


(* -- Security notions -- *)
module EUF_CMA_MFORSTWESNPRF (A : Adv_EUFCMA_MFORSTWESNPRF, O : Oracle_CMA_MFORSTWESNPRF) = {
  proc main() : bool = {    
    var ad : adrs;
    var ps : pseed;
    var pk : pkFORS list list * pseed * adrs;
    var sk : skFORS list list * pseed * adrs;
    var m : msg;
    var sig : mkey * sigFORSTW;
    var is_valid, is_fresh : bool;

    ad <- witness;
    ps <$ dpseed;
    
    (pk, sk) <@ M_FORS_TW_ES_NPRF.keygen(ps, ad);

    O.init(sk);

    (m, sig) <@ A(O).forge(pk);

    is_valid <@ M_FORS_TW_ES_NPRF.verify(pk, m, sig);

    is_fresh <@ O.fresh(m);

    return is_valid /\ is_fresh; 
  }
}.


(* -- Oracle implementations -- *)
(* Default implementation of CMA oracle used for EUF_CMA_MFORSTWESNPRF  *)
module O_CMA_MFORSTWESNPRF : Oracle_CMA_MFORSTWESNPRF = {
  var sk : skFORS list list * pseed * adrs
  var qs : msg list

  proc init(sk_init : skFORS list list * pseed * adrs) : unit = {
    sk <- sk_init;
    qs <- [];
  }

  proc sign(m : msg) : mkey * sigFORSTW = {
    var sig : mkey * sigFORSTW;

    sig <@ M_FORS_TW_ES_NPRF.sign(sk, m);

    qs <- rcons qs m;

    return sig;
  }
    
  proc fresh(m : msg) : bool = {
    return ! m \in qs;
  }

  proc nr_queries() : int = {
    return size qs;
  }
}.

(* 
  As O_CMA_MFORSTWESNPRF, but additionally keeps track of 
  all indices resulting from applying the message compression on 
  the queried messaged
*) 
module O_CMA_MFORSTWESNPRF_AV : Oracle_CMA_MFORSTWESNPRF = {
  include var O_CMA_MFORSTWESNPRF [-init, sign]
  var lidxs : (int * int * int) list
  
  proc init(sk_init : skFORS list list * pseed * adrs) : unit = {
    O_CMA_MFORSTWESNPRF.init(sk_init);
    lidxs <- [];
  }

  proc sign(m : msg) : mkey * sigFORSTW = {
    var mk : mkey;
    var sigFORSTW : sigFORSTW;

    (mk, sigFORSTW) <@ O_CMA_MFORSTWESNPRF.sign(m);

    lidxs <- lidxs ++ g (mco mk m);

    return (mk, sigFORSTW);
  }
}.


(* -- Reduction adversaries -- *)
module (R_EUFCMA_ITSR (A : Adv_EUFCMA_MFORSTWESNPRF) : Adv_ITSR) (O : Oracle_ITSR) = {  
  var ps : pseed
  var ad : adrs
  var skFORSs : skFORS list list

  module O_CMA_R_EUFCMA_ITSR : SOracle_CMA_MFORSTWESNPRF = {    
    proc sign(m : msg) : mkey * sigFORSTW = {
      var mk : mkey;
      var cm : msgFORSTW;
      var idx : iid;
      var tidx, kpidx : int;
      var skFORS : skFORS;
      var sigFORSTW : sigFORSTW;
       
      mk <@ O.query(m);
      
      (cm, idx) <- mco mk m;
    
      (tidx, kpidx) <- edivz (val idx) l;

      skFORS <- nth witness (nth witness skFORSs tidx) kpidx;

      sigFORSTW <@ FL_FORS_TW_ES_NPRF.sign((skFORS, ps, set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx), cm);
    
      return (mk, sigFORSTW);
    }
  }
  
  proc find() : mkey * msg = {
    var pk : pkFORS list list * pseed * adrs;
    var sk : skFORS list list * pseed * adrs;
    var mk' : mkey;
    var m' : msg;
    var sig' : mkey * sigFORSTW;
    
    ad <- witness;
    ps <$ dpseed;
    
    (pk, sk) <@ M_FORS_TW_ES_NPRF.keygen(ps, ad);    
    
    skFORSs <- sk.`1;
    
    (m', sig') <@ A(O_CMA_R_EUFCMA_ITSR).forge(pk);
    
    mk' <- sig'.`1;
    
    return (mk', m');
  }
}.

(* 
  One of the cases for forgery of FORS-TW is that one of the private key elements
  in the signature was not included in the responses to the adversary's queries, but it does
  map to the original corresnding leaf. Then, there are two possibilities:
  1. The private key element is the same as the original one. 
  2. The private key element is different than the original one.
  In the first case, we cannot directly reduce to PRE because this does not allow for
  answering signature queries from the FORS-TW adversary (since we would not know the
  private key elements corresponding to the leaves as these would be the pre-image
  challenges). So, we need to reduce to TopenPRE, which in turn reduces
  to DSPR + TCR (see DSPR/SPHINCS+ paper); might be able to directly reduce (i.e., not go via TopenPRE)
  In the second case, we can reduce to SMDTTCR.
*)
module (R_EUFCMA_FSMDTOpenPREC (A : Adv_EUFCMA_MFORSTWESNPRF) : FC_OpenPRE.Adv_SMDTOpenPREC) (O : FC_OpenPRE.Oracle_SMDTOpenPRE, OC : FC.Oracle_THFC) = {
  var ps : pseed
  var ad : adrs
  var leavess : dgstblock list list list list
  var lidxs : (int * int * int) list
  
  module O_CMA_R_EUFCMA_FSMDTOpenPREC : SOracle_CMA_MFORSTWESNPRF = {
    (* Signing as with FORS-TW (No PRF), but obtain secret key elements from OpenPRE oracle *)
    proc sign(m : msg) : mkey * sigFORSTW = {
      var mk : mkey;
      var cm : msgFORSTW;
      var idx : iid;
      var tidx, kpidx, lidx : int;
      var bslidx : bool list;
      var sigFORS : (dgstblock * apFORSTW) list;
      var leaves : dgstblock list;
      var skFORS_ele : dgst;
      var ap : apFORSTW;
      
      mk <$ dmkey;

      (cm, idx) <- mco mk m;

      (tidx, kpidx) <- edivz (val idx) l;

      sigFORS <- [];
      while (size sigFORS < k) {
        bslidx <- take a (drop (a * (size sigFORS)) (val cm));  
        lidx <- bs2int (rev bslidx);
        skFORS_ele <@ O.open(tidx * l * k * t + kpidx * k * t + size sigFORS * t + lidx);
        leaves <- nth witness (nth witness (nth witness leavess tidx) kpidx) (size sigFORS);
        ap <- cons_ap_trh ps ad (list2tree leaves) lidx (size sigFORS);
        sigFORS <- rcons sigFORS (DigestBlock.insubd skFORS_ele, ap);
      }
      
      lidxs <- lidxs ++ g (cm, idx);
      
      return (mk, insubd sigFORS);
    }
  }

  proc pick() : unit = {
    var leaf : dgstblock;
    var leavest : dgstblock list;
    var leavesk : dgstblock list list;
    var leavesl : dgstblock list list list;
    
    (* Pick address *)
    ad <- witness;
    
    (* 
      Sample FORS-TW secret keys, specify each secret key element as target 
      and obtain corresponding leaves
    *)
    leavess <- [];
    (* For each set of FORS-TW instances (SPHINCS+: XMSS instance)... *)
    while (size leavess < s) {
      leavesl <- [];
      (* For each FORS-TW instance in a set (SPHINCS+: leaf of XMSS instance)... *)
      while (size leavesl < l) {
        leavesk <- [];
        (* For each tree in a FORS-TW instance... *)
        while (size leavesk < k)  {
          leavest <- [];
          (* Obtain the leaves by querying challenge oracle *)
          while (size leavest < t) {
            leaf <@ O.query(set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) (size leavess)) (size leavesl)) 0 (size leavesk * t + size leavest));
            leavest <- rcons leavest leaf;
          }
          leavesk <- rcons leavesk leavest;
        }
        leavesl <- rcons leavesl leavesk;
      }
      leavess <- rcons leavess leavesl;
    }
  }
  
  proc find(ps_init : pseed) : int * dgst = {
    var pkFORSs : pkFORS list list;
    var pkFORSl : pkFORS list;
    var pkFORS : pkFORS;
    var roots : dgstblock list;
    var root : dgstblock;
    var leaves : dgstblock list;
    var m' : msg;
    var mk' : mkey;
    var sigFORS' : sigFORSTW;
    var mksigFORS' : mkey * sigFORSTW;
    var lidxs' : (int * int * int) list;
    var tidx, kpidx, dfidx, cidx : int;
    var cm' : msgFORSTW;
    var idx' : iid;
    var x' : dgstblock;
    var ap' : apFORSTW;
    
    (* Initialize module variables (for oracle use) *)
    ps <- ps_init;
    lidxs <- [];
    
    (* Compute public keys corresponding to previously computed secret keys/leaves *)
    pkFORSs <- [];
    while (size pkFORSs < s) {
      pkFORSl <- [];
      while (size pkFORSl < l) {
        roots <- [];
        while (size roots < k) {
          leaves <- nth witness (nth witness (nth witness leavess (size pkFORSs)) (size pkFORSl)) (size roots);
          root <- val_bt_trh ps (set_kpidx (set_tidx (set_typeidx ad trhtype) (size pkFORSs)) (size pkFORSl)) (list2tree leaves) (size roots);
          roots <- rcons roots root;
        }
        pkFORS <- trco ps (set_kpidx (set_tidx (set_typeidx ad trcotype) (size pkFORSs)) (size pkFORSl)) (flatten (map DigestBlock.val roots));
        
        pkFORSl <- rcons pkFORSl pkFORS;
      }
      pkFORSs <- rcons pkFORSs pkFORSl;
    }

    (* Ask adversary to forge *)
    (m', mksigFORS') <@ A(O_CMA_R_EUFCMA_FSMDTOpenPREC).forge((pkFORSs, ps, ad));
    
    (* Compress message and extract instance index *)
    (mk', sigFORS') <- mksigFORS';
    (cm', idx') <- mco mk' m';
    
    (* 
      Compute (instance index, inner tree index, leaf index) tuples from 
      the compressed message and instance index 
    *)
    lidxs' <- g (cm', idx');
    
    (* 
      Find the (instance index, inner tree index, leaf index) tuple computed from
      the forgery message that did not yet occur in the tuples computed from 
      the messages in the oracle queries. From this tuple, extract the inner tree
      index (which is also the index of the element in the forged signature
      that we want to extract)
    *)
    dfidx <- (nth witness lidxs' (find (fun i => ! i \in lidxs) lidxs')).`2;
    
    (* Get element from forged signature containing the non-matching secret key element  *)
    (x', ap') <- nth witness (val sigFORS') dfidx;

    (* Compute (outer) tree and keypair index from instance index *)
    (tidx, kpidx) <- edivz (val idx') l;
    
    (* 
      Compute index in the target list of the OpenPRE oracle for which x' is a collision.
      Since we queried the targets in order, starting from the left, this index is exactly
      the index of the secret key/leaf (for which x' is a collision) if you were to
      flatten the complete structure.
    *)
    cidx <- tidx * l * k * t + kpidx * k * t + dfidx * t + bs2int (rev (take a (drop (a * dfidx) (val cm'))));

    return (cidx, val x');
  }
}.

module (R_EUFCMA_FSMDTTCRC (A : Adv_EUFCMA_MFORSTWESNPRF) : FC_TCR.Adv_SMDTTCRC) (O : FC_TCR.Oracle_SMDTTCR, OC : FC.Oracle_THFC) = {
  var ad : adrs
  var skFORSs : skFORS list list
  var leavess : dgstblock list list list list
    
  proc pick() : unit = {
    var skFORS : skFORS;
    var skFORSl : skFORS list;
    var leaf : dgstblock;
    var leavest : dgstblock list;
    var leavesk : dgstblock list list;
    var leavesl : dgstblock list list list;
    
    (* Pick address *)
    ad <- witness;
    
    (* 
      Sample FORS-TW secret keys, specify each secret key element as target 
      and obtain corresponding leaves
    *)
    skFORSs <- [];
    leavess <- [];
    (* For each set of FORS-TW instances (SPHINCS+: XMSS instance)... *)
    while (size skFORSs < s) {
      skFORSl <- [];
      leavesl <- [];
      (* For each FORS-TW instance in a set (SPHINCS+: leaf of XMSS instance)... *)
      while (size skFORSl < l) {
        skFORS <$ dskFORS;
        
        leavesk <- [];
        
        (* For each tree in a FORS-TW instance... *)
        while (size leavesk < k)  {
          leavest <- [];
          (* Compute the leaves by querying challenge oracle on secret key elements *)
          while (size leavest < t) {
            leaf <@ O.query(set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) (size skFORSs)) (size skFORSl)) 0 (size leavesk * t + size leavest), 
                            val (nth witness (nth witness (val skFORS) (size leavesk)) (size leavest)));
            leavest <- rcons leavest leaf;
          }
          leavesk <- rcons leavesk leavest;
        }
        skFORSl <- rcons skFORSl skFORS;
        leavesl <- rcons leavesl leavesk;
      }
      skFORSs <- rcons skFORSs skFORSl;
      leavess <- rcons leavess leavesl;
    }
  }
  
  proc find(ps : pseed) : int * dgst = {
    var pkFORS : pkFORS;
    var pkFORSl : pkFORS list;
    var pkFORSs : pkFORS list list;
    var leaves : dgstblock list;
    var root : dgstblock;
    var roots : dgstblock list;
    var m' : msg;
    var mk' : mkey;
    var sigFORS' : sigFORSTW;
    var mksigFORS' : mkey * sigFORSTW;
    var tidx, kpidx, dfidx, cidx : int;
    var cm' : msgFORSTW;
    var idx' : iid;
    var x' : dgstblock;
    var ap' : apFORSTW;
    var lidxs' : (int * int * int) list;
    
    (* Initialize CMA oracle *)
    O_CMA_MFORSTWESNPRF_AV.init((skFORSs, ps, ad));
    
    (* Compute public keys corresponding to previously computed secret keys/leaves *)
    pkFORSs <- [];
    while (size pkFORSs < s) {
      pkFORSl <- [];
      while (size pkFORSl < l) {
        roots <- [];
        while (size roots < k) {
          leaves <- nth witness (nth witness (nth witness leavess (size pkFORSs)) (size pkFORSl)) (size roots);
          root <- val_bt_trh ps (set_kpidx (set_tidx (set_typeidx ad trhtype) (size pkFORSs)) (size pkFORSl)) (list2tree leaves) (size roots);
          roots <- rcons roots root;
        }
        pkFORS <- trco ps (set_kpidx (set_tidx (set_typeidx ad trcotype) (size pkFORSs)) (size pkFORSl)) (flatten (map DigestBlock.val roots));
        
        pkFORSl <- rcons pkFORSl pkFORS;
      }
      pkFORSs <- rcons pkFORSs pkFORSl;
    }

    (* Ask adversary to forge *)
    (m', mksigFORS') <@ A(O_CMA_MFORSTWESNPRF_AV).forge((pkFORSs, ps, ad));
    
    (* Compress message and extract instance index *)
    (mk', sigFORS') <- mksigFORS';
    (cm', idx') <- mco mk' m';
    
    (* 
      Compute (instance index, inner tree index, leaf index) tuples from 
      the compressed message and instance index 
    *)
    lidxs' <- g (cm', idx');
    
    (* 
      Find the (instance index, inner tree index, leaf index) tuple computed from
      the forgery message that did not yet occur in the tuples computed from 
      the messages in the oracle queries. From this tuple, extract the inner tree
      index (which is also the index of the element in the forged signature
      that we want to extract)
    *)
    dfidx <- (nth witness lidxs' (find (fun i => ! i \in O_CMA_MFORSTWESNPRF_AV.lidxs) lidxs')).`2;
    
    (* Get element from forged signature containing the non-matching secret key element (pointed to by dfidx) *)
    (x', ap') <- nth witness (val sigFORS') dfidx;

    (* Compute (outer) tree and keypair index from instance index *)
    (tidx, kpidx) <- edivz (val idx') l;
    
    (* 
      Compute index of the element in the target list of the OpenPRE oracle for which x' is a collision.
      Note that, if you were to flatten the whole structure, i.e., sequence all (trees of) considered 
      FORS-TW instances, we have effectively queried the leaves from left to right.
    *)
    cidx <- tidx * l * k * t + kpidx * k * t + dfidx * t + bs2int (rev (take a (drop (a * dfidx) (val cm'))));

    return (cidx, val x');
  }
}.


module (R_EUFCMA_TRHSMDTTCRC (A : Adv_EUFCMA_MFORSTWESNPRF) : TRHC_TCR.Adv_SMDTTCRC) (O : TRHC_TCR.Oracle_SMDTTCR, OC : TRHC.Oracle_THFC) = {
  var ad : adrs
  var skFORSs : skFORS list list
  var leavess : dgstblock list list list list
  var nodess : dgstblock list list list list list
  var rootss : dgstblock list list list
  
  proc pick() : unit = {
    var skFORS : skFORS;
    var skFORSl : skFORS list;
    var leaf, lnode, rnode, node : dgstblock;
    var leavest, nodespl, nodescl, rootsk : dgstblock list;
    var leavesk, nodest, rootsl : dgstblock list list;
    var leavesl, nodesk : dgstblock list list list;
    var nodesl : dgstblock list list list list;
    
    (* Pick address *)
    ad <- witness;
    
    (* Sample FORS-TW secret keys and compute corresponding leaves *)
    skFORSs <- [];
    leavess <- [];
    (* For each set of FORS-TW instances (SPHINCS+: XMSS instance)... *)
    while (size skFORSs < s) {
      skFORSl <- [];
      leavesl <- [];
      (* For each FORS-TW instance in a set (SPHINCS+: leaf of XMSS instance)... *)
      while (size skFORSl < l) {
        skFORS <$ dskFORS;
        
        leavesk <- [];
        
        (* For each tree in a FORS-TW instance... *)
        while (size leavesk < k)  {
          leavest <- [];
          (* Compute the leaves by querying challenge oracle on secret key elements *)
          while (size leavest < t) {
            leaf <@ OC.query(set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) (size skFORSs)) (size skFORSl)) 
                                         0 (size leavesk * t + size leavest), 
                             val (nth witness (nth witness (val skFORS) (size leavesk)) (size leavest)));
            leavest <- rcons leavest leaf;
          }
          leavesk <- rcons leavesk leavest;
        }
        skFORSl <- rcons skFORSl skFORS;
        leavesl <- rcons leavesl leavesk;
      }
      skFORSs <- rcons skFORSs skFORSl;
      leavess <- rcons leavess leavesl;
    }

    (* 
      Compute nodes of trees corresponding to leaves, 
      specifying all concatenations of sibling nodes as targets 
    *)
    nodess <- [];
    rootss <- [];
    (* For each set of FORS-TW instances (SPHINCS+: XMSS instance)... *)
    while (size nodess < s) {
      nodesl <- [];
      rootsl <- [];
      (* For each FORS-TW instance in a set (SPHINCS+: leaf of XMSS instance)... *)
      while (size nodesl < l) {
        nodesk <- [];
        rootsk <- [];
        
        (* For each tree in a FORS-TW instance... *)
        while (size nodesk < k) { 
          nodest <- [];
          leavest <- nth witness (nth witness (nth witness leavess (size nodess)) (size nodesl)) (size nodesk);
          (* For each layer in a tree (of a FORS-TW instance)... *)
          while (size nodest < a) {
            (* Get nodes from the previous layer *)
            nodespl <- last leavest nodest;
            
            (* 
              Compute the nodes in the current layer by mapping the (concatenations of sibling) nodes
              from the previous layer, specifying each of these (concatenations of) nodes as targets
            *)
            nodescl <- [];
            while (size nodescl < 2 ^ (a - size nodest - 1)) {
              lnode <- nth witness nodespl (2 * size nodescl);
              rnode <- nth witness nodespl (2 * size nodescl + 1);
              
              node <@ O.query(set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) (size nodess)) (size nodesl)) 
                                          (size nodest + 1) (size nodesk * nr_nodes (size nodest + 1) + size nodescl), 
                              val lnode ++ val rnode);
              
              nodescl <- rcons nodescl node; 
            }
            nodest <- rcons nodest nodescl;
          }
          nodesk <- rcons nodesk nodest;
          rootsk <- rcons rootsk (nth witness (nth witness nodest (a - 1)) 0); (* Final computed node is the root *)
        }
        nodesl <- rcons nodesl nodesk;
        rootsl <- rcons rootsl rootsk;
      }
      nodess <- rcons nodess nodesl;
      rootss <- rcons rootss rootsl;
    }
  }
  
  proc find(ps : pseed) : int * dgst = {
    var pkFORS : pkFORS;
    var pkFORSl : pkFORS list;
    var pkFORSs : pkFORS list list;
    var skFORS : skFORS;
    var leaves, sleaves, sleaves' : dgstblock list;
    var root : dgstblock;
    var roots : dgstblock list;
    var m' : msg;
    var mk' : mkey;
    var sigFORS' : sigFORSTW;
    var mksigFORS' : mkey * sigFORSTW;
    var tidx, kpidx, hidx, bidx, dfidx, cidx : int;
    var cm' : msgFORSTW;
    var idx' : iid;
    var x' : dgstblock;
    var ap' : apFORSTW;
    var leavesk : dgstblock list list;
    var leaf' : dgstblock;
    var bs' : bool list;
    var idx'' : int;
    var c : dgst;
    var lidxs' : (int * int * int) list;
    var cr;
    
    (* Initialize CMA oracle *)
    O_CMA_MFORSTWESNPRF_AV.init((skFORSs, ps, ad));
    
    (* Compute public keys corresponding to previously computed roots *)
    pkFORSs <- [];
    while (size pkFORSs < s) {
      pkFORSl <- [];
      while (size pkFORSl < l) {
        roots <- nth witness (nth witness rootss (size pkFORSs)) (size pkFORSl);
        pkFORS <- trco ps (set_kpidx (set_tidx (set_typeidx ad trcotype) (size pkFORSs)) (size pkFORSl)) (flatten (map DigestBlock.val roots));
        pkFORSl <- rcons pkFORSl pkFORS;
      }
      pkFORSs <- rcons pkFORSs pkFORSl;
    }

    (* Ask adversary to forge *)
    (m', mksigFORS') <@ A(O_CMA_MFORSTWESNPRF).forge((pkFORSs, ps, ad));
    
    (* Compress message and extract instance index *)
    (mk', sigFORS') <- mksigFORS';
    (cm', idx') <- mco mk' m';
    
    (* 
      Compute (instance index, inner tree index, leaf index) tuples from 
      the compressed message and instance index 
    *)
    lidxs' <- g (cm', idx');
    
    (* 
      Find the (instance index, inner tree index, leaf index) tuple computed from
      the forgery message that did not yet occur in the tuples computed from 
      the messages in the oracle queries. From this tuple, extract the inner tree
      index (which is also the index of the element in the forged signature
      that we want to extract)
    *)
    dfidx <- (nth witness lidxs' (find (fun i => ! i \in O_CMA_MFORSTWESNPRF_AV.lidxs) lidxs')).`2;

    (* Compute (outer) tree and keypair index from instance index *)
    (tidx, kpidx) <- edivz (val idx') l;

    (* Construct non-matching leaf from non-matching secret key value in forgery (pointed to by dfidx) *) 
    leaf' <- f ps (set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx) 0 (dfidx * t + (bs2int (rev (take a (drop (a * dfidx) (val cm')))))))
               (val (nth witness (unzip1 (val sigFORS')) dfidx));

    (* Get (original) leaves of tree pointed to by dfidx in instance pointed to by kpidx in set pointed to by tidx *)
    leaves <- nth witness (nth witness (nth witness leavess tidx) kpidx) dfidx;
        
    (* 
      Get element from forged signature containing non-matching secret key element 
      that maps to non-matching leaf  
    *)
    (x', ap') <- nth witness (val sigFORS') dfidx;
    
    (* Extract colliding values from the original tree and the non-matching leaf/authentication path *)
    cr <- extract_collision_bt_ap_trh ps (set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx) 
                                      (list2tree leaves) (val ap') (take a (drop (a * dfidx) (val cm'))) 
                                      leaf' dfidx;
    
    (* Collision from leaf/authentication path *)
    c <- val cr.`3 ++ val cr.`4;
    
    (* Height and breadth indices of address under which the extracted values collide *)
    (hidx, bidx) <- cr.`5;
    
    (* 
      Compute index of the element in the target list of the SMDDTTCR oracle for which c is a collision.
      Note that, if you were to flatten the whole structure, i.e., sequence all (trees of) considered 
      FORS-TW instances, we have effectively queried the complete trees from left to right; for each 
      tree, have effectively queried bottom-up layer-wise; and, for each layer, we
      queried from left to right.
    *)
    cidx <- tidx * l * k * (2 ^ a - 1) + kpidx * k * (2 ^ a - 1) + dfidx * (2 ^ a - 1) 
            + sumz (mkseq (fun (i : int) => nr_nodes (i + 1)) (hidx - 1)) + (bidx %% nr_nodes hidx);

    return (cidx, c);
  }
}.

module (R_EUFCMA_TRCOSMDTTCRC (A : Adv_EUFCMA_MFORSTWESNPRF) : TRCOC_TCR.Adv_SMDTTCRC) (O : TRCOC_TCR.Oracle_SMDTTCR, OC : TRCOC.Oracle_THFC) = {
  var ad : adrs
  var skFORSs : skFORS list list
  var leavess : dgstblock list list list list
  var rootss : dgstblock list list list
  var pkFORSs : pkFORS list list
    
  proc pick() : unit = {
    var skFORS : skFORS;
    var skFORSl : skFORS list;
    var leaf, lnode, rnode, node, root : dgstblock;
    var leavest, nodespl, nodescl, rootsk : dgstblock list;
    var leavesk, nodest, rootsl : dgstblock list list;
    var leavesl, nodesk : dgstblock list list list;
    var nodesl : dgstblock list list list list;
    var pkFORS : pkFORS;
    var pkFORSl : pkFORS list;
    
    (* Pick address *)
    ad <- witness;
    
    (* Sample FORS-TW secret keys and compute corresponding leaves *)
    skFORSs <- [];
    leavess <- [];
    (* For each set of FORS-TW instances (SPHINCS+: XMSS instance)... *)
    while (size skFORSs < s) {
      skFORSl <- [];
      leavesl <- [];
      (* For each FORS-TW instance in a set (SPHINCS+: leaf of XMSS instance)... *)
      while (size skFORSl < l) {
        skFORS <$ dskFORS;
        
        leavesk <- [];
        
        (* For each tree in a FORS-TW instance... *)
        while (size leavesk < k)  {
          leavest <- [];
          (* Compute the leaves by querying challenge oracle on secret key elements *)
          while (size leavest < t) {
            leaf <@ OC.query(set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) (size skFORSs)) (size skFORSl)) 
                                         0 (size leavesk * t + size leavest), 
                             val (nth witness (nth witness (val skFORS) (size leavesk)) (size leavest)));
            leavest <- rcons leavest leaf;
          }
          leavesk <- rcons leavesk leavest;
        }
        skFORSl <- rcons skFORSl skFORS;
        leavesl <- rcons leavesl leavesk;
      }
      skFORSs <- rcons skFORSs skFORSl;
      leavess <- rcons leavess leavesl;
    }

    (* Compute nodes of trees corresponding to leaves *)
    rootss <- [];
    (* For each set of FORS-TW instances (SPHINCS+: XMSS instance)... *)
    while (size rootss < s) {
      rootsl <- [];
      (* For each FORS-TW instance in a set (SPHINCS+: leaf of XMSS instance)... *)
      while (size rootsl < l) {
        rootsk <- [];
        (* For each tree in a FORS-TW instance... *)
        while (size rootsk < k) { 
          nodest <- [];
          leavest <- nth witness (nth witness (nth witness leavess (size rootss)) (size rootsl)) (size rootsk);
          (* For each layer in a tree (of a FORS-TW instance)... *)
          while (size nodest < a) {
            (* Get nodes from the previous layer *)
            nodespl <- last leavest nodest;
            
            (* 
              Compute the nodes in the current layer by mapping the (concatenations of sibling) nodes
              from the previous layer, specifying each of these (concatenations of) nodes as targets
            *)
            nodescl <- [];
            while (size nodescl < 2 ^ (a - size nodest - 1)) {
              lnode <- nth witness nodespl (2 * size nodescl);
              rnode <- nth witness nodespl (2 * size nodescl + 1);
              
              node <@ OC.query(set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) (size rootss)) (size rootsl)) 
                                           (size nodest + 1) (size rootsk * nr_nodes (size nodest + 1) + size nodescl), 
                               val lnode ++ val rnode);
              
              nodescl <- rcons nodescl node; 
            }
            nodest <- rcons nodest nodescl;
          }
          rootsk <- rcons rootsk (nth witness (nth witness nodest (a - 1)) 0); (* Final computed node is the root *)
        }
        rootsl <- rcons rootsl rootsk;
      }
      rootss <- rcons rootss rootsl;
    }
    
    (* 
      Compute public keys corresponding of FORS-TW instances, specifying 
      (concatenation of) roots of each instance as targets.
    *)
    pkFORSs <- [];
    while (size pkFORSs < s) {
      pkFORSl <- [];
      while (size pkFORSl < l) {
        rootsk <- nth witness (nth witness rootss (size pkFORSs)) (size pkFORSl);
        pkFORS <@ O.query(set_kpidx (set_tidx (set_typeidx ad trcotype) (size pkFORSs)) (size pkFORSl), 
                          flatten (map DigestBlock.val rootsk));
        pkFORSl <- rcons pkFORSl pkFORS;
      }
      pkFORSs <- rcons pkFORSs pkFORSl;
    }
  }
  
  proc find(ps : pseed) : int * dgst = {
    var skFORS : skFORS;
    var leaves, sleaves, sleaves' : dgstblock list;
    var root : dgstblock;
    var roots : dgstblock list;
    var m' : msg;
    var mk' : mkey;
    var sigFORS' : sigFORSTW;
    var mksigFORS' : mkey * sigFORSTW;
    var tidx, kpidx, cidx : int;
    var cm' : msgFORSTW;
    var idx' : iid;
    var skFORSels : dgstblock list;
    var roots' : dgstblock list;
    var c : dgst;
    
    (* Initialize CMA oracle *)
    O_CMA_MFORSTWESNPRF.init((skFORSs, ps, ad));
        
    (* Ask adversary to forge *)
    (m', mksigFORS') <@ A(O_CMA_MFORSTWESNPRF).forge((pkFORSs, ps, ad));
    
    (* Compress message and extract instance index *)
    (mk', sigFORS') <- mksigFORS';
    (cm', idx') <- mco mk' m';
    
    (* Compute (outer) tree and keypair index from instance index *)
    (tidx, kpidx) <- edivz (val idx') l;
    
    (* Get (list of) roots of instance pointed to by kpidx in set pointed to by tidx *)
    roots' <- nth witness (nth witness rootss tidx) kpidx;
    
    (* Compute the collision as the concatenation of the roots *)
    c <- flatten (map DigestBlock.val roots');
    
    (* 
      Compute index of element in the target list of the SMDDTTCR oracle for which c is a collision.
      Note that, if you were to flatten the whole structure, i.e., sequence all (trees of) considered 
      FORS-TW instances, we have effectively queried (the concatenation of) the roots of each FORS-TW
      instance from left to right.
    *)
    cidx <- val idx';
    
    return (cidx, c);
  }
}.

section Proof_EUFCMA_M_FORS_TW_ES.

declare module A <: Adv_EUFCMA_MFORSTWESNPRF {-O_CMA_MFORSTWESNPRF, -O_ITSR_Default, -O_SMDTOpenPRE_Default, -FC_TCR.O_SMDTTCR_Default, -TRHC_TCR.O_SMDTTCR_Default, -TRCOC_TCR.O_SMDTTCR_Default, -O_THFC_Default, -R_EUFCMA_ITSR, -R_EUFCMA_FSMDTOpenPREC, -R_EUFCMA_FSMDTTCRC, -R_EUFCMA_TRHSMDTTCRC, -R_EUFCMA_TRCOSMDTTCRC}.

(* 
  Immediately replace while loops (primarily inner ones) in reduction adversaries
  by the appropriate functional operators utilizing the public seed ps that is used in the oracles.
  To this end, create auxiliary game that is equivalent to original game, but stores ps in a module variable
  (instead of a local variable) and have reduction adversaries directly use this. 
*)



local lemma EUFCMA_MFORSTWESNPRF_OpenPRE &m:
  Pr[EUF_CMA_MFORSTWESNPRF(A, O_CMA_MFORSTWESNPRF).main() @ &m : res] 
  <= 
  Pr[ITSR(R_EUFCMA_ITSR(A), O_ITSR_Default).main() @ &m : res]
  +
  Pr[FC_OpenPRE.SM_DT_OpenPRE_C(R_EUFCMA_FSMDTOpenPREC(A), FC_OpenPRE.O_SMDTOpenPRE_Default, FC.O_THFC_Default).main() @ &m : res]
  +
  Pr[FC_TCR.SM_DT_TCR_C(R_EUFCMA_FSMDTTCRC(A), FC_TCR.O_SMDTTCR_Default, FC.O_THFC_Default).main() @ &m : res]
  + 
  Pr[TRHC_TCR.SM_DT_TCR_C(R_EUFCMA_TRHSMDTTCRC(A), TRHC_TCR.O_SMDTTCR_Default, TRHC.O_THFC_Default).main() @ &m : res]
  +
  Pr[TRCOC_TCR.SM_DT_TCR_C(R_EUFCMA_TRCOSMDTTCRC(A), TRCOC_TCR.O_SMDTTCR_Default, TRCOC.O_THFC_Default).main() @ &m : res].
proof.
admit.
qed.

(* 
  TODO: 
  Need finiteness and uniform distribution over input type.
  In the case of f, this is dgst, but this is currently equal to bool list, an infinite type.
  However, this is only the input type for f to model that is part of the colleciton thfc.
  Effectively, f has input type ddgstblock (because it is used on dgst elements that are of length 8 * n and
  hence satisfy the condition of ddgstblock), which is indeed finite...
*)
(*
local clone import OpenPRE_From_TCR_DSPR_THF as OPRETCRDSPR with
*)
end section Proof_EUFCMA_M_FORS_TW_ES.
