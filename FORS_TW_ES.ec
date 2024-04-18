(* - Require/Import - *)
(* -- Built-In (Standard Library) -- *)
require import AllCore List Distr SmtMap DList FinType IntDiv BitEncoding StdOrder StdBigop LoopTransform.
(*---*) import BS2Int BitChunking Bigint BIA.
(*---*) import RealOrder.


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



(* - Types (1/3) - *)
(* -- General -- *)
(* Instance index *)
clone import Subtype as Index with
  type T <= int,
    op P i <= 0 <= i < d
    
  proof *.
  realize inhabited by exists 0; smt(ge1_d).

type index = Index.sT.

(* Seeds for message compression key generation function *)
type mseed.

(* Randomness for non-deterministic signature generation
type rm.
*)

(* Keys for message compression *)
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

(* Proper distribution over randomness for non-deterministic signature generation
op [lossless] drm : rm distr.
*)
 
(* Proper distribution over randomness for message compression *)
op [lossless] dmkey : mkey distr.

(* Proper distribution over public seeds *)
op [lossless] dpseed : pseed distr.

(*
(* Proper distribution over secret seeds *)
op [lossless] dsseed : sseed distr.
*)

(* Proper, full, and uniform distribution over digests of length 1 (block of 8 * n bits) *)
op [lossless full uniform] ddgstblock : dgstblock distr.

(* Proper distribution over digests of length 1 (block of 8 * n bits), lifted to dgst type *)
op ddgstblocklift : dgst distr = dmap ddgstblock DigestBlock.val.

lemma ddgstblocklift_ll : is_lossless ddgstblocklift.
proof. by rewrite dmap_ll ddgstblock_ll. qed.

(*
(* 
  Proper distribution that samples a FORS secret key by independently sampling
  each individual secret key element independently from ddgstblock
*)
op dskFORS : skFORS distr = dmap (dlist (dlist ddgstblock t) k) DBLLKTL.insubd.

lemma dskFORS_ll : is_lossless dskFORS.
proof. by rewrite dmap_ll 2!dlist_ll ddgstblock_ll. qed.
*)


(* - Types (2/3) - *)
(* -- General -- *)
(* Addresses used in tweakable hash functions *)
clone import HashAddresses as HA with
  type index <= int,
    op l <- adrs_len,
    op valid_idxvals <- valid_idxvals,
    op valid_adrsidxs <- valid_adrsidxs
    
    proof ge1_l by smt(ge5_adrslen).
    
import Adrs.

type adrs = HA.adrs.



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

(* Initialization ("zero") address *)
const adz : { adrs | valid_fadrs adz } as valf_adz.


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

op get_typeidx (ad : adrs) : int =
  get_idx ad 3.


(* -- Keyed Hash Functions -- *)
(* Secret key element generation function *)
op skg : sseed -> (pseed * adrs) -> dgstblock.

(*
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
*)  

(* --- Message compression --- *)
(* Message compression key geneneration function
op mkg : mseed -> (rm * msg) -> mkey.
*)
op mkg : mseed -> msg -> mkey.


(*
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
*)

(* Message compression function *)
op mco : mkey -> msg -> msgFORSTW * index.

(* 
  Function mapping output of message compression function to a list
  containing three-tuples of which the entries respectively signify the following.
  - The index of a key set (i.e., pointer to a specific FORS-TW instance).
  - The index of a secret value set (i.e., pointer to Merkle tree in FORS-TW instance indicated by first value of tuple). 
  - The index of a secret value (i.e., pointer to a leaf of the Merkle tree indicated by second value of tuple). 
*)
op g (mi : msgFORSTW * index) : (int * int * int) list =
  let cmsg = chunk a (val mi.`1) in
  let idx = val mi.`2 in
    mkseq (fun (i : int) => (idx, i, bs2int (rev (nth witness cmsg i)))) k.

clone KeyedHashFunctions as MCO with
  type key_t <- mkey,
  type in_t <- msg,
  type out_t <- msgFORSTW * index,
  
    op f <- mco
    
  proof *.
  
clone import MCO.ITSR as MCO_ITSR with  
(*
  op ks <- d,
  op svsks <- k,
  op svsvs <- t,
*)  
  op g <- g,
  
  op dkey <- dmkey
  
  proof *.
(*
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
*)  
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
clone import F.SMDTOpenPRE as F_OpenPRE with
  op t_smdtopenpre <- d * k * t,
  
  op din <- ddgstblocklift
    
  proof *.
  realize ge0_tsmdtopenpre by smt(ge1_d ge1_k ge2_t).
  realize din_ll by exact: ddgstblocklift_ll.

clone import F.Collection as FC with
  type diff_t <- int,
  
    op get_diff <- size,
    
    op fc <- thfc
    
  proof *.
  realize in_collection by exists (8 * n).
(*
clone import FC.SMDTOpenPREC as FC_OpenPRE with
  op t_smdtopenpre <- d * k * t,
  
  op din <- ddgstblocklift
    
  proof *.
  realize ge0_tsmdtopenpre by smt(ge1_d ge1_k ge2_t).
  realize din_ll by exact: ddgstblocklift_ll.
*)    
clone import FC.SMDTTCRC as FC_TCR with
  op t_smdttcr <- d * k * t
  
  proof *.
  realize ge0_tsmdttcr by smt(ge1_d ge1_k ge2_t).

(* (Explicitly) Domain-restricted version of f; used for DSPR-related proofs  *)
op f' (ps : pseed) (ad : adrs) (x : dgstblock) : dgstblock = 
  f ps ad (val x).

clone import OpenPRE_From_TCR_DSPR_THF as FP_OPRETCRDSPR with
  type pp_t <- pseed,
  type tw_t <- adrs,
  type in_t <- dgstblock,
  type out_t <- dgstblock,
      
    op f <- f',
    
    op t <- d * k * t,
    
    op dpp <- dpseed,
    op din <- ddgstblock,
    
  theory InFT <= DigestBlockFT
  
  rename [theory] "F" as "FP"
  rename [theory] "F_OpenPRE" as "FP_OpenPRE"
  rename [theory] "F_TCR" as "FP_TCR"
  rename [theory] "F_DSPR" as "FP_DSPR" 
  
  proof *.
  realize dpp_ll by exact: dpseed_ll.
  realize din_ll by exact: ddgstblock_ll.
  realize din_fu by exact: ddgstblock_fu.
  realize din_uni by exact: ddgstblock_uni.
  realize ge0_t by smt(ge2_t ge1_k ge1_d).

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
  height index a, and breadth index bidx. Here, idx should be a valid leaf index (i.e., in [0, 2 ^ a - 1])
  and bidx should be a valid breadth index for root nodes of the Merkle trees in a FORS-TW 
  instance (i.e., in [0, k - 1]).
*)
op val_ap_trh (ap : apFORSTWTW) (idx : int) (leaf : dgstblock) (ps : pseed) (ad : adrs) (bidx : int) : dgstblock = 
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



(* - Types (3/3) - *)
(* 
  FORS-TW addresses 
  Only used to select arbitrary valid FORS-TW in security notion/reductions 

clone import Subtype as FHA with
  type T <= adrs,
    op P ad <= valid_fadrs ad. 
  
type fadrs = FHA.sT.
*)

lemma gettype_setthtbkptypetrh (i j u v : int) (ad : adrs) :
     valid_fidxvalsgp (drop 5 (val ad))
  => valid_tidx (nth witness (val ad) 4)
  => valid_tidx i
  => valid_kpidx j
  => valid_thidx u
  => valid_tbidx u v
  => get_typeidx (set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) i) j) u v) = trhtype.
proof.
have gtif_szad : forall i, i < 5 => i < if 5 < size (val ad) then 5 else size (val ad) by smt(Adrs.valP ge5_adrslen).
move=> vadgp vti vi vj vu vv @/get_typeidx @/set_typeidx @/set_tidx @/set_idx; rewrite insubdK. 
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  rewrite /valid_fidxvals /valid_fidxvalslp 4?drop_put_out 1..4:// ?take_put /=.
  rewrite /valid_fidxvalslptrco /valid_fidxvalslptrh.
  rewrite ?nth_put ?size_put ?size_take 1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39://
          1..20:gtif_szad 1..40:// /= ?nth_take 1..2:// /=; smt(ge1_a ge1_k ge1_l IntOrder.expr_gt0).
rewrite /set_kpidx /set_idx insubdK.
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  rewrite /valid_fidxvals /valid_fidxvalslp 5?drop_put_out 1..5:// ?take_put /=.
  rewrite /valid_fidxvalslptrco /valid_fidxvalslptrh.
  by rewrite ?nth_put ?size_put ?size_take 1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,
             37,39,41,43,45,47,49:// 1..25:gtif_szad 1..50:// /=; smt(ge1_a ge1_k IntOrder.expr_gt0). 
rewrite /set_thtbidx /set_idx insubdK.
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  rewrite /valid_fidxvals /valid_fidxvalslp ?drop_put_out 1..6:// ?take_put /=.
  rewrite /valid_fidxvalslptrco /valid_fidxvalslptrh.
  by rewrite ?nth_put ?size_put ?size_take
             1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,45,47,49,51,53,55,
             57,59:// 1..30:gtif_szad 1..60:// /= vi vj /=; smt(ge1_a ge1_k IntOrder.expr_gt0).
rewrite /get_idx insubdK. 
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  rewrite /valid_fidxvals /valid_fidxvalslp ?drop_put_out 1..8:// ?take_put /=.
  rewrite /valid_fidxvalslptrco /valid_fidxvalslptrh.
  by rewrite ?nth_put ?size_put ?size_take
             1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,45,47,49,51,53,55,
             57,59,61,63,65,67,69,71,73,75,77,79,81:// 1..40:gtif_szad 1..80:// /=; smt(ge1_a ge1_k IntOrder.expr_gt0).
by rewrite ?nth_put ?size_put 9:// /#.  
qed.


lemma gettype_setkp2type2trhtrco (i j j' : int) (ad : adrs) :
     valid_fidxvalsgp (drop 5 (val ad))
  => valid_tidx (nth witness (val ad) 4)
  => valid_tidx i
  => valid_kpidx j
  => valid_kpidx j'
  => get_typeidx (set_kpidx (set_typeidx (set_kpidx (set_tidx (set_typeidx ad trhtype) i) j) trcotype) j') = trcotype.
proof.
have gtif_szad : forall i, i < 5 => i < if 5 < size (val ad) then 5 else size (val ad) by smt(Adrs.valP ge5_adrslen).
move=> vadgp vti vi vj vjp @/get_typeidx @/set_typeidx @/set_tidx @/set_idx.
rewrite (insubdK (put _ _ trhtype)). 
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  rewrite /valid_fidxvals /valid_fidxvalslp 4?drop_put_out 1..4:// ?take_put /=.
  rewrite /valid_fidxvalslptrco /valid_fidxvalslptrh.
  rewrite ?nth_put ?size_put ?size_take 1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39://
          1..20:gtif_szad 1..40:// /= ?nth_take 1..2:// /=; smt(ge1_a ge1_k ge1_l IntOrder.expr_gt0).
rewrite /set_kpidx /set_idx (insubdK (put _ 4 i)).
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  rewrite /valid_fidxvals /valid_fidxvalslp 5?drop_put_out 1..5:// ?take_put /=.
  rewrite /valid_fidxvalslptrco /valid_fidxvalslptrh.
  by rewrite ?nth_put ?size_put ?size_take 1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,
             37,39,41,43,45,47,49:// 1..25:gtif_szad 1..50:// /=; smt(ge1_a ge1_k IntOrder.expr_gt0). 
rewrite (insubdK (put _ 2 j)).
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  rewrite /valid_fidxvals /valid_fidxvalslp ?drop_put_out 1..6:// ?take_put /=.
  rewrite /valid_fidxvalslptrco /valid_fidxvalslptrh.
  by rewrite ?nth_put ?size_put ?size_take
             1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,45,47,49,51,53,55,
             57,59:// 1..30:gtif_szad 1..60:// /= vi vj /=; smt(ge1_a ge1_k IntOrder.expr_gt0).
rewrite insubdK. 
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  rewrite /valid_fidxvals /valid_fidxvalslp ?drop_put_out 1..10:// ?take_put /=.
  rewrite /valid_fidxvalslptrco /valid_fidxvalslptrh.
  by rewrite ?nth_put ?size_put ?size_take
             1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,45,47,49,51,53,55,
             57,59,61,63,65,67,69,71,73,75,77,79,81,83,85,87,89,91,93,95,97,99:// 
             1..50:gtif_szad 1..100:// /=; smt(ge1_a ge1_k IntOrder.expr_gt0).
rewrite /get_idx insubdK. 
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  rewrite /valid_fidxvals /valid_fidxvalslp ?drop_put_out 1..11:// ?take_put /=.
  rewrite /valid_fidxvalslptrco /valid_fidxvalslptrh.
  by rewrite ?nth_put ?size_put ?size_take
             1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,45,47,49,51,53,55,
             57,59,61,63,65,67,69,71,73,75,77,79,81,83,85,87,89,91,93,95,97,99,101,103,105,107,109://
             1..55:gtif_szad 1..110:// /=; smt(ge1_a ge1_k IntOrder.expr_gt0).
by rewrite ?nth_put ?size_put 12:// /#.  
qed.



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
    var mk : mkey;
    var cm : msgFORSTW;
    var idx : index;
    var tidx, kpidx : int;
    var sig : sigFORSTW;
    
    (ms, ss, ps, ad) <- sk;
    
    (* rm <$ drm; *)
    (* mk <- mkg ms (rm, m); *)
    mk <- mkg ms m;
    
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
    var idx : index;
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
  
  proc gen_skFORS() : skFORS = {
    var skFORS_ele : dgstblock;
    var skFORSt : dgstblock list;
    var skFORS : dgstblock list list;
    
    skFORS <- [];
    while (size skFORS < k) {
      skFORSt <- [];
      while (size skFORSt < t) {
        skFORS_ele <$ ddgstblock;
        skFORSt <- rcons skFORSt skFORS_ele;
      }
      skFORS <- rcons skFORS skFORSt;  
    }
    
    return insubd skFORS;
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
    var ms : mseed;
    var pkFORS : pkFORS;
    var skFORS : skFORS;
    var pk : pkFORSTW;
    var sk : skFORS * pseed * adrs;
    
    skFORS <@ gen_skFORS();
    
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
  
  proc verify = FL_FORS_TW_ES.verify
(*  
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
*) 
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
        skFORS <@ FL_FORS_TW_ES_NPRF.gen_skFORS();
        pkFORS <@ FL_FORS_TW_ES_NPRF.gen_pkFORS(skFORS, ps, set_kpidx (set_tidx (set_typeidx ad trhtype) (size skFORSs)) (size skFORSl));
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
(*  
  proc sign(sk : skFORS list list * pseed * adrs, m : msg) : mkey * sigFORSTW = {
    var skFORS : skFORS;
    var skFORSs : skFORS list list;
    var ps : pseed;
    var ad : adrs;
    var mk : mkey;
    var cm : msgFORSTW;
    var idx : index;
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
*)  
  proc verify = M_FORS_TW_ES.verify
(*  
  proc verify(pk : pkFORS list list * pseed * adrs, m : msg, sig : mkey * sigFORSTW) : bool = {
    var pkFORS : pkFORS;
    var pkFORSs : pkFORS list list;
    var ps : pseed;
    var ad : adrs;
    var mk : mkey;
    var sigFORSTWTW : sigFORSTW;
    var cm : msgFORSTW;
    var idx : index;
    var tidx, kpidx : int;
    var is_valid : bool; 
        
    (pkFORSs, ps, ad) <- pk;
    (mk, sigFORSTWTW) <- sig;
    
    (cm, idx) <- mco mk m;
    
    (tidx, kpidx) <- edivz (val idx) l;
    
    pkFORS <- nth witness (nth witness pkFORSs tidx) kpidx;
    
    is_valid <@ FL_FORS_TW_ES_NPRF.verify((pkFORS, ps, set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx), cm, sigFORSTWTW);
    
    return is_valid;
  }
*) 
}.




(* - Proof - *)
(*
(* -- Import of relevant definitions and properties --  *)
clone import DigitalSignatures as DSS_MFORSTWESNPRF with
  type pk_t <- pkFORS list list * pseed * adrs,
  type sk_t <- skFORS list list * pseed * adrs,
  type msg_t <- msg,
  type sig_t <- mkey * sigFORSTWTW
  
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
  
  proc sign(m : msg) : mkey * sigFORSTWTW = {
    var mk : mkey;
    var sigFORSTWTW : sigFORSTWTW;
    
    (mk, sigFORSTWTW) <@ O_CMA_MFORSTWESNPRF.sign(m);
    
    lidxs <- lidxs ++ g (mco mk m);
    
    return (mk, sigFORSTWTW);  
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
    var m' : msg;
    var sig' : mkey * sigFORSTW;
    var is_valid, is_fresh : bool;

    ad <- adz;
    ps <$ dpseed;
    
    (pk, sk) <@ M_FORS_TW_ES_NPRF.keygen(ps, ad);

    O.init(sk);

    (m', sig') <@ A(O).forge(pk);

    is_valid <@ M_FORS_TW_ES_NPRF.verify(pk, m', sig');

    is_fresh <@ O.fresh(m');

    return is_valid /\ is_fresh; 
  }
}.


(* -- Oracle implementations -- *)
(* Default implementation of CMA oracle used for EUF_CMA_MFORSTWESNPRF  *)
module O_CMA_MFORSTWESNPRF : Oracle_CMA_MFORSTWESNPRF = {
  var sk : skFORS list list * pseed * adrs
  var qs : msg list
  (*var rmmap : (rm * msg, mkey) fmap *)
  var mmap : (msg, mkey) fmap
  
  proc init(sk_init : skFORS list list * pseed * adrs) : unit = {
    sk <- sk_init;
    qs <- [];
    mmap <- empty;
  }

  proc sign(m : msg) : mkey * sigFORSTW = {
    var skFORS : skFORS;
    var skFORSs : skFORS list list;
    var ps : pseed;
    var ad : adrs;
    var mk : mkey;
    var cm : msgFORSTW;
    var idx : index;
    var tidx, kpidx : int;
    var sigFORSTW : sigFORSTW;
    
    (skFORSs, ps, ad) <- sk;
    
    (* rm <$ drm; *)
    
    if (m \notin mmap) { 
      mk <$ dmkey;
      mmap.[m] <- mk;
    }
    mk <- oget mmap.[m];
      
    (cm, idx) <- mco mk m;
    
    (tidx, kpidx) <- edivz (val idx) l;
    
    skFORS <- nth witness (nth witness skFORSs tidx) kpidx;
     
    sigFORSTW <@ FL_FORS_TW_ES_NPRF.sign((skFORS, ps, set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx), cm);
    
    qs <- rcons qs m;

    return (mk, sigFORSTW);
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
  var mks : mkey list
  var lidxs : (int * int * int) list
  
  proc init(sk_init : skFORS list list * pseed * adrs) : unit = {
    O_CMA_MFORSTWESNPRF.init(sk_init);
    mks <- [];
    lidxs <- [];
  }

  proc sign(m : msg) : mkey * sigFORSTW = {
    var skFORS : skFORS;
    var skFORSs : skFORS list list;
    var ps : pseed;
    var ad : adrs;
    var mk : mkey;
    var cm : msgFORSTW;
    var idx : index;
    var tidx, kpidx : int;
    var sigFORSTW : sigFORSTW;
    
    (skFORSs, ps, ad) <- sk;
    
    if (m \notin mmap) { 
      mk <$ dmkey;
      mmap.[m] <- mk;
      mks <- rcons mks mk;
      lidxs <- lidxs ++ g (mco mk m);
      qs <- rcons qs m;
    }
    mk <- oget mmap.[m];
      
    (cm, idx) <- mco mk m;
    
    (tidx, kpidx) <- edivz (val idx) l;
    
    skFORS <- nth witness (nth witness skFORSs tidx) kpidx;
     
    sigFORSTW <@ FL_FORS_TW_ES_NPRF.sign((skFORS, ps, set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx), cm);

    return (mk, sigFORSTW);
  }
}.

(* -- Reduction adversaries -- *)
module (R_ITSR_EUFCMA (A : Adv_EUFCMA_MFORSTWESNPRF) : Adv_ITSR) (O : Oracle_ITSR) = {  
  var ps : pseed
  var ad : adrs
  var skFORSs : skFORS list list
  var mmap : (msg, mkey) fmap
  
  module O_CMA_R_EUFCMA_ITSR : SOracle_CMA_MFORSTWESNPRF = {    
    proc sign(m : msg) : mkey * sigFORSTW = {
      var mk : mkey;
      var cm : msgFORSTW;
      var idx : index;
      var tidx, kpidx : int;
      var skFORS : skFORS;
      var sigFORSTW : sigFORSTW;
      
      if (m \notin mmap) {  
        mk <@ O.query(m);
        mmap.[m] <- mk;
      }
      mk <- oget mmap.[m]; 
      
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
    
    ad <- adz;
    ps <$ dpseed;
    
    (pk, sk) <@ M_FORS_TW_ES_NPRF.keygen(ps, ad);    
    
    skFORSs <- sk.`1;
    mmap <- empty;
    
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
module (R_FSMDTOpenPREC_EUFCMA (A : Adv_EUFCMA_MFORSTWESNPRF) : FC_OpenPRE.Adv_SMDTOpenPREC) (O : FC_OpenPRE.Oracle_SMDTOpenPRE, OC : FC.Oracle_THFC) = {
  var ps : pseed
  var ad : adrs
  var leavess : dgstblock list list list list
  var lidxs : (int * int * int) list
  (* var rmmap : (rm * msg, mkey) fmap *)
  var mmap : (msg, mkey) fmap
  
  module O_CMA_R_FSMDTOpenPREC_EUFCMA : SOracle_CMA_MFORSTWESNPRF = {
    (* Signing as with FORS-TW (No PRF), but obtain secret key elements from OpenPRE oracle *)
    proc sign(m : msg) : mkey * sigFORSTW = {
      var mk : mkey;
      var cm : msgFORSTW;
      var idx : index;
      var tidx, kpidx, lidx : int;
      var bslidx : bool list;
      var sigFORSTW : (dgstblock * apFORSTW) list;
      var leaves : dgstblock list;
      var skFORS_ele : dgst;
      var ap : apFORSTW;
      
      (* rm <$ drm; *)
    
      if (m \notin mmap) { 
        mk <$ dmkey;
        mmap.[m] <- mk;
      } else {
        mk <- oget mmap.[m];
      }

      (cm, idx) <- mco mk m;

      (tidx, kpidx) <- edivz (val idx) l;

      sigFORSTW <- [];
      while (size sigFORSTW < k) {
        bslidx <- take a (drop (a * (size sigFORSTW)) (val cm));  
        lidx <- bs2int (rev bslidx);
        skFORS_ele <@ O.open(tidx * l * k * t + kpidx * k * t + size sigFORSTW * t + lidx);
        leaves <- nth witness (nth witness (nth witness leavess tidx) kpidx) (size sigFORSTW);
        ap <- cons_ap_trh ps ad (list2tree leaves) lidx (size sigFORSTW);
        sigFORSTW <- rcons sigFORSTW (DigestBlock.insubd skFORS_ele, ap);
      }
      
      lidxs <- lidxs ++ g (cm, idx);
      
      return (mk, insubd sigFORSTW);
    }
  }

  proc pick() : unit = {
    var leaf : dgstblock;
    var leavest : dgstblock list;
    var leavesk : dgstblock list list;
    var leavesl : dgstblock list list list;
    
    (* Pick address *)
    ad <- adz;
    
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
    var sigFORSTW' : sigFORSTW;
    var mksigFORSTW' : mkey * sigFORSTW;
    var lidxs' : (int * int * int) list;
    var tidx, kpidx, dfidx, cidx : int;
    var cm' : msgFORSTW;
    var idx' : index;
    var x' : dgstblock;
    var ap' : apFORSTW;
    
    (* Initialize module variables (for oracle use) *)
    ps <- ps_init;
    lidxs <- [];
    mmap <- empty;
    
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
    (m', mksigFORSTW') <@ A(O_CMA_R_FSMDTOpenPREC_EUFCMA).forge((pkFORSs, ps, ad));
    
    (* Compress message and extract instance index *)
    (mk', sigFORSTW') <- mksigFORSTW';
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
    (x', ap') <- nth witness (val sigFORSTW') dfidx;

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
*)

module (R_FSMDTOpenPRE_EUFCMA (A : Adv_EUFCMA_MFORSTWESNPRF) : F_OpenPRE.Adv_SMDTOpenPRE) (O : F_OpenPRE.Oracle_SMDTOpenPRE) = {
  var ps : pseed
  var ad : adrs
  var lidxs : (int * int * int) list
  var leavess : dgstblock list
  (* var rmmap : (rm * msg, mkey) fmap *)
  var mmap : (msg, mkey) fmap
  
  module O_CMA : SOracle_CMA_MFORSTWESNPRF = {
    (* Signing as with FORS-TW (No PRF), but obtain secret key elements from OpenPRE oracle *)
    proc sign(m : msg) : mkey * sigFORSTW = {
      var mk : mkey;
      var cm : msgFORSTW;
      var idx : index;
      var tidx, kpidx, lidx : int;
      var bslidx : bool list;
      var sigFORSTW : (dgstblock * apFORSTW) list;
      var leaves : dgstblock list;
      var skFORS_ele : dgst;
      var ap : apFORSTW;
      
      (* rm <$ drm; *)
    
      if (m \notin mmap) { 
        mk <$ dmkey;
        mmap.[m] <- mk;
        lidxs <- lidxs ++ g (mco mk m);
      }
      mk <- oget mmap.[m];

      (cm, idx) <- mco mk m;

      (tidx, kpidx) <- edivz (val idx) l;

      sigFORSTW <- [];
      while (size sigFORSTW < k) {
        bslidx <- take a (drop (a * (size sigFORSTW)) (val cm));  
        lidx <- bs2int (rev bslidx);
        skFORS_ele <@ O.open(tidx * l * k * t + kpidx * k * t + size sigFORSTW * t + lidx);
        (* leaves <- nth witness (nth witness (nth witness leavess tidx) kpidx) (size sigFORSTW); *)
        leaves <- take t (drop (tidx * l * k * t + kpidx * k * t + size sigFORSTW * t) leavess);
        ap <- cons_ap_trh ps (set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx) (list2tree leaves) lidx (size sigFORSTW);
        sigFORSTW <- rcons sigFORSTW (DigestBlock.insubd skFORS_ele, ap);
      }
      
      return (mk, insubd sigFORSTW);
    }
  }

  proc pick() : adrs list = {
    var adl : adrs list;
    var tidx, kpidx, tbidx : int;
    
    (* Pick address *)
    ad <- adz;
    
    adl <- [];
    tidx <- 0;
    while (tidx < s) {
      kpidx <- 0;
      while (kpidx < l) {
        tbidx <- 0;
        while (tbidx < k * t) {
          adl <- rcons adl (set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx) 0 tbidx);
          tbidx <- tbidx + 1;
        }
        kpidx <- kpidx + 1;
      }
      tidx <- tidx + 1;
    }
    
    return adl;  
  }
  
  proc find(ps_init : pseed, leavess_init : dgstblock list) : int * dgst = {
    var pkFORSs : pkFORS list list;
    var pkFORSl : pkFORS list;
    var pkFORS : pkFORS;
    var roots : dgstblock list;
    var root : dgstblock;
    var leaves : dgstblock list;
    var m' : msg;
    var mk' : mkey;
    var sigFORSTW' : sigFORSTW;
    var mksigFORSTW' : mkey * sigFORSTW;
    var lidxs' : (int * int * int) list;
    var tidx, kpidx, dfidx, dftidx, dflfidx, cidx : int;
    var cm' : msgFORSTW;
    var idx' : index;
    var x' : dgstblock;
    var ap' : apFORSTW;
    
    (* Initialize module variables (for oracle use) *)
    ps <- ps_init;
    leavess <- leavess_init;
    lidxs <- [];
    mmap <- empty;

    (*
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
    *)
    
    (* Compute public keys corresponding to previously computed secret keys/leaves *)
    pkFORSs <- [];
    while (size pkFORSs < s) {
      pkFORSl <- [];
      while (size pkFORSl < l) {
        roots <- [];
        while (size roots < k) {
       (* leaves <- nth witness (nth witness (nth witness leavess (size pkFORSs)) (size pkFORSl)) (size roots); *)
          leaves <- take t (drop (size pkFORSs * l * k * t + size pkFORSl * k * t + size roots * t) leavess); 
          root <- val_bt_trh ps (set_kpidx (set_tidx (set_typeidx ad trhtype) (size pkFORSs)) (size pkFORSl)) (list2tree leaves) (size roots);
          roots <- rcons roots root;
        }
        pkFORS <- trco ps (set_kpidx (set_tidx (set_typeidx ad trcotype) (size pkFORSs)) (size pkFORSl)) (flatten (map DigestBlock.val roots));
        
        pkFORSl <- rcons pkFORSl pkFORS;
      }
      pkFORSs <- rcons pkFORSs pkFORSl;
    }

    (* Ask adversary to forge *)
    (m', mksigFORSTW') <@ A(O_CMA).forge((pkFORSs, ps, ad));
    
    (* Compress message and extract instance index *)
    (mk', sigFORSTW') <- mksigFORSTW';
    (cm', idx') <- mco mk' m';
    
    (* 
      Compute (instance index, inner tree index, leaf index) tuples from 
      the compressed message and instance index 
    *)
    lidxs' <- g (cm', idx');
    
    (* 
      Find the (instance index, inner tree index, leaf index) tuple computed from
      the forgery message that did not yet occur in the tuples computed from 
      the messages in the oracle queries.
    *)
    (dfidx, dftidx, dflfidx) <- nth witness lidxs' (find (fun i => ! i \in lidxs) lidxs');
    
    (* Get element from forged signature containing the non-matching secret key element  *)
    (x', ap') <- nth witness (val sigFORSTW') dftidx;

    (* Compute (outer) tree and keypair index from instance index *)
    (tidx, kpidx) <- edivz (val idx') l;
    
    (* 
      Compute index in the target list of the OpenPRE oracle for which x' is a collision.
      Since we queried the targets in order, starting from the left, this index is exactly
      the index of the secret key/leaf (for which x' is a collision) if you were to
      flatten the complete structure.
    *)
    cidx <- tidx * l * k * t + kpidx * k * t + dftidx * t + dflfidx; (* bs2int (rev (take a (drop (a * dfidx) (val cm')))) *)

    return (cidx, val x');
  }
}.

module (R_FPOpenPRE_FOpenPRE (A :  Adv_EUFCMA_MFORSTWESNPRF) : FP_OpenPRE.Adv_SMDTOpenPRE) (O : FP_OpenPRE.Oracle_SMDTOpenPRE) = {
  module O_SMDTOpenPRE : F_OpenPRE.Oracle_SMDTOpenPRE = {
    include var F_OpenPRE.O_SMDTOpenPRE_Default [-open]     
    
    proc open(i : int) : dgst ={
      var x : dgstblock;
      
      x <@ O.open(i);
      
      return val x;
    }
  }
  
  proc pick() : adrs list = {
    var adl : adrs list;
    
    adl <@ R_FSMDTOpenPRE_EUFCMA(A, O_SMDTOpenPRE).pick();
    
    return adl;
  }
  
  proc find(ps : pseed, ys : dgstblock list) : int * dgstblock = {
    var i : int;
    var x : dgst;
    
    (i, x) <@ R_FSMDTOpenPRE_EUFCMA(A, O_SMDTOpenPRE).find(ps, ys);
    
    return (i, DigestBlock.insubd x);
  }
}.
 
(*
module (R_FSMDTTCRC_EUFCMA (A : Adv_EUFCMA_MFORSTWESNPRF) : FC_TCR.Adv_SMDTTCRC) (O : FC_TCR.Oracle_SMDTTCR, OC : FC.Oracle_THFC) = {
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
    ad <- adz;
    
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
        skFORS <@ FL_FORS_TW_ES_NPRF.gen_skFORS();
        
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
    var sigFORSTW' : sigFORSTW;
    var mksigFORSTW' : mkey * sigFORSTW;
    var tidx, kpidx, dfidx, cidx : int;
    var cm' : msgFORSTW;
    var idx' : index;
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
    (m', mksigFORSTW') <@ A(O_CMA_MFORSTWESNPRF_AV).forge((pkFORSs, ps, ad));
    
    (* Compress message and extract instance index *)
    (mk', sigFORSTW') <- mksigFORSTW';
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
    (x', ap') <- nth witness (val sigFORSTW') dfidx;

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
*)

module (R_TRHSMDTTCRC_EUFCMA (A : Adv_EUFCMA_MFORSTWESNPRF) : TRHC_TCR.Adv_SMDTTCRC) (O : TRHC_TCR.Oracle_SMDTTCR, OC : TRHC.Oracle_THFC) = {
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
    ad <- adz;
    
    (* Sample FORS-TW secret keys and compute corresponding leaves *)
    skFORSs <- [];
    leavess <- [];
    (* For each set of FORS-TW instances (SPHINCS+: XMSS instance)... *)
    while (size skFORSs < s) {
      skFORSl <- [];
      leavesl <- [];
      (* For each FORS-TW instance in a set (SPHINCS+: leaf of XMSS instance)... *)
      while (size skFORSl < l) {
        skFORS <@ FL_FORS_TW_ES_NPRF.gen_skFORS();
        
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
            while (size nodescl < nr_nodes (size nodest + 1)) {
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
    var sigFORSTW' : sigFORSTW;
    var mksigFORSTW' : mkey * sigFORSTW;
    var tidx, kpidx, hidx, bidx, dfidx, cidx : int;
    var cm' : msgFORSTW;
    var idx' : index;
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
    (m', mksigFORSTW') <@ A(O_CMA_MFORSTWESNPRF).forge((pkFORSs, ps, ad));
    
    (* Compress message and extract instance index *)
    (mk', sigFORSTW') <- mksigFORSTW';
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
               (val (nth witness (unzip1 (val sigFORSTW')) dfidx));

    (* Get (original) leaves of tree pointed to by dfidx in instance pointed to by kpidx in set pointed to by tidx *)
    leaves <- nth witness (nth witness (nth witness leavess tidx) kpidx) dfidx;
        
    (* 
      Get element from forged signature containing non-matching secret key element 
      that maps to non-matching leaf  
    *)
    (x', ap') <- nth witness (val sigFORSTW') dfidx;
    
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
            + bigi predT (fun (i : int) => nr_nodes i) 1 hidx + (bidx %% nr_nodes hidx);

    return (cidx, c);
  }
}.


module (R_TRCOSMDTTCRC_EUFCMA (A : Adv_EUFCMA_MFORSTWESNPRF) : TRCOC_TCR.Adv_SMDTTCRC) (O : TRCOC_TCR.Oracle_SMDTTCR, OC : TRCOC.Oracle_THFC) = {
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
    ad <- adz;
    
    (* Sample FORS-TW secret keys and compute corresponding leaves *)
    skFORSs <- [];
    leavess <- [];
    (* For each set of FORS-TW instances (SPHINCS+: XMSS instance)... *)
    while (size skFORSs < s) {
      skFORSl <- [];
      leavesl <- [];
      (* For each FORS-TW instance in a set (SPHINCS+: leaf of XMSS instance)... *)
      while (size skFORSl < l) {
        skFORS <@ FL_FORS_TW_ES_NPRF.gen_skFORS();
        
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
            while (size nodescl < nr_nodes (size nodest + 1)) {
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
    var sigFORSTW' : sigFORSTW;
    var mksigFORSTW' : mkey * sigFORSTW;
    var tidx, kpidx, cidx : int;
    var cm' : msgFORSTW;
    var idx' : index;
    var skFORSels : dgstblock list;
    var roots' : dgstblock list;
    var c : dgst;
    
    (* Initialize CMA oracle *)
    O_CMA_MFORSTWESNPRF.init((skFORSs, ps, ad));
        
    (* Ask adversary to forge *)
    (m', mksigFORSTW') <@ A(O_CMA_MFORSTWESNPRF).forge((pkFORSs, ps, ad));
    
    (* Compress message and extract instance index *)
    (mk', sigFORSTW') <- mksigFORSTW';
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

declare module A <: Adv_EUFCMA_MFORSTWESNPRF {-O_CMA_MFORSTWESNPRF, -O_ITSR_Default, -F_OpenPRE.O_SMDTOpenPRE_Default, -FP_OpenPRE.O_SMDTOpenPRE_Default, -FP_DSPR.O_SMDTDSPR_Default, -FC_TCR.O_SMDTTCR_Default, -TRHC_TCR.O_SMDTTCR_Default, -TRCOC_TCR.O_SMDTTCR_Default, -O_THFC_Default, -R_ITSR_EUFCMA, -R_FSMDTOpenPRE_EUFCMA, -R_TRHSMDTTCRC_EUFCMA, -R_TRCOSMDTTCRC_EUFCMA}.

declare axiom A_forge_ll (O <: SOracle_CMA_MFORSTWESNPRF{-A}) :
  islossless O.sign => islossless A(O).forge.

(* As EUF_CMA_MFORSTWESNPRF, but with additional checks for possibility of breaking considered properties of THFs  *)
local module EUF_CMA_MFORSTWESNPRF_C = {
  var valid_ITSR, valid_OpenPRE, valid_TRHTCR : bool
  
  proc main() : bool = {    
    var ad : adrs;
    var ps : pseed;
    var pk : pkFORS list list * pseed * adrs;
    var sk : skFORS list list * pseed * adrs;
    var m' : msg;
    var sig' : mkey * sigFORSTW;
    var is_valid, is_fresh : bool;
    var skFORSt, leaves : dgstblock list;
    var skFORS : skFORS;
    var pkFORSs : pkFORS list list;
    var skFORSs : skFORS list list; 
    var mk' : mkey;
    var sigFORSTW' : sigFORSTW;
    var lidxs' : (int * int * int) list;
    var dfidx, dftidx, dflfidx, tidx, kpidx : int;
    var x, x', leaf, leaf', root, root' : dgstblock;
    var ap' : apFORSTW;
    
    ad <- adz;
    ps <$ dpseed;
    
    (pk, sk) <@ M_FORS_TW_ES_NPRF.keygen(ps, ad);

    O_CMA_MFORSTWESNPRF_AV.init(sk);

    (m', sig') <@ A(O_CMA_MFORSTWESNPRF_AV).forge(pk);

    is_valid <@ M_FORS_TW_ES_NPRF.verify(pk, m', sig');

    is_fresh <@ O_CMA_MFORSTWESNPRF_AV.fresh(m');
    
    (* Additional checks *)
    (* 
      ITSR: 
      The adversary managed to find a message that, when signed, only uses secret key values that
      have already been revealed as part of signatures of different, previously signed messages 
    *)
    (mk', sigFORSTW') <- sig';
    lidxs' <- g (mco mk' m');
    valid_ITSR <-    (forall idx, idx \in lidxs' => idx \in O_CMA_MFORSTWESNPRF_AV.lidxs) 
                  /\ ! (mk', m') \in zip O_CMA_MFORSTWESNPRF_AV.mks O_CMA_MFORSTWESNPRF.qs;
    
    
    (*
      OpenPRE (assuming no ITSR break):
      Even though the signed message uses a secret key value that was not yet revealed (i.e., no ITSR break),
      the adversary managed to find a value that maps to the same leaf as this original secret key value.  
    *)
    skFORSs <- sk.`1;
    (dfidx, dftidx, dflfidx) <- nth witness lidxs' (find (fun i => ! i \in O_CMA_MFORSTWESNPRF_AV.lidxs) lidxs');
    (x', ap') <- nth witness (val sigFORSTW') dftidx;
    (tidx, kpidx) <- edivz dfidx l;
    skFORS <- nth witness (nth witness skFORSs tidx) kpidx;
    skFORSt <- nth witness (val skFORS) dftidx; 
    x <- nth witness skFORSt dflfidx;
    leaf' <- f ps (set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx) 0 (dftidx * t + dflfidx)) (val x');
    leaf <- f ps (set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx) 0 (dftidx * t + dflfidx)) (val x);
    valid_OpenPRE <- leaf' = leaf;  
    
    (*
      Tree-hash TCR (assuming no ITSR and no OpenPRE breaks):
      Even though there is a leaf (computed from the secret key value) in the forged signature that does not match
      the corresponding original leaf, the adversary managed to find an authentication path that still results in the
      same root as the original tree's root (which requires a collision for the tree hash function). 
    *) 
    root' <- val_ap_trh ps (set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx) ap' dflfidx leaf' dftidx; 
    leaves <- mkseq (fun (i : int) => f ps (set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx) 0 (dftidx * t + i)) (val (nth witness skFORSt i))) t;
    root <- val_bt_trh ps (set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx) (list2tree leaves) dflfidx;
    valid_TRHTCR <- root' = root;
    
    return is_valid /\ is_fresh; 
  }
}.

local equiv Eqv_EUF_CMA_MFORSTWESNPRF_Orig_C:
  EUF_CMA_MFORSTWESNPRF(A, O_CMA_MFORSTWESNPRF).main ~ EUF_CMA_MFORSTWESNPRF_C.main :
    ={glob A} ==> ={res}.
proof.
proc.
seq 5 5 : (   ={sig', pk, m'} 
           /\ mem O_CMA_MFORSTWESNPRF.qs{1} = mem O_CMA_MFORSTWESNPRF.qs{2}). 
+ call (:   ={O_CMA_MFORSTWESNPRF.mmap, O_CMA_MFORSTWESNPRF.sk}
         /\ mem O_CMA_MFORSTWESNPRF.qs{1} = mem O_CMA_MFORSTWESNPRF.qs{2}
         /\ dom O_CMA_MFORSTWESNPRF.mmap{1} = mem O_CMA_MFORSTWESNPRF.qs{1}).
  - proc; inline *.
    sp 1 1.
    if => //.
    * wp=> /=. 
      while (={ps0, ad0, skFORS0, m0, sig}).
      + wp => /=.
        by while (={leaves0, skFORS1, idxt, ps1, ad1}); wp; skip.
      wp => /=.
      by rnd; skip => />; smt(mem_set mem_rcons).
    wp => /=.
    while (={ps0, ad0, skFORS0, m0, sig}).
    + wp => /=.
      by while (={leaves0, skFORS1, idxt, ps1, ad1}); wp; skip.
    by wp; skip => />; smt(mem_set mem_rcons).
  inline{1} 4; inline{2} 4; inline{2} 5.
  wp => />.
  conseq (: _ ==> ={pk, sk}); 1: smt(mem_empty).
  by sim.
inline{1} 2; inline{2} 2.
wp => /=.
conseq (: _ ==> ={is_valid}); 1: smt(). 
by sim.
qed.


(* As EUF_CMA_MFORSTWESNPRF, but with additional checks for possibility of breaking considered properties of THFs  *)
local module EUF_CMA_MFORSTWESNPRF_V = {
  var valid_ITSR, valid_OpenPRE, valid_TRHTCR : bool
  
  proc main() : bool = {    
    var ad : adrs;
    var ps : pseed;
    var pk : pkFORS list list * pseed * adrs;
    var sk : skFORS list list * pseed * adrs;
    var m' : msg;
    var sig' : mkey * sigFORSTW;
    var is_valid, is_fresh : bool;
    var skFORSt, leaves : dgstblock list;
    var skFORS : skFORS;
    var pkFORS, pkFORS' : pkFORS;
    var pkFORSs : pkFORS list list;
    var skFORSs : skFORS list list; 
    var mk' : mkey;
    var cm' : msgFORSTW;
    var idx' : index;
    var sigFORSTW' : sigFORSTW;
    var lidxs' : (int * int * int) list;
    var dfidx, dftidx, dflfidx, tidx, kpidx, lfidx : int;
    var x, x', leaf, leaf', root, root' : dgstblock;
    var ap' : apFORSTW;
    var skFORS_ele' : dgstblock;
    var skFORS_eles', leaves' : dgstblock list;
    var roots' : dgstblock list;
    
    ad <- adz;
    ps <$ dpseed;
    
    (pk, sk) <@ M_FORS_TW_ES_NPRF.keygen(ps, ad);

    O_CMA_MFORSTWESNPRF_AV.init(sk);

    (m', sig') <@ A(O_CMA_MFORSTWESNPRF_AV).forge(pk);
    
    pkFORSs <- pk.`1;
    (mk', sigFORSTW') <- sig';
    (cm', idx') <- mco mk' m';
    (tidx, kpidx) <- edivz (val idx') l;
    pkFORS <- nth witness (nth witness pkFORSs tidx) kpidx;
    lidxs' <- g (cm', idx');
    
    skFORS_eles' <- [];
    leaves' <- [];
    roots' <- [];
    while (size roots' < k){
      lfidx <- (nth witness lidxs' (size roots')).`3;
      (skFORS_ele', ap') <- nth witness (val sigFORSTW') (size roots');
      leaf' <- f ps (set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx) 0 (size roots' * t + lfidx)) (val skFORS_ele');
      root' <- val_ap_trh ps (set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx) ap' lfidx leaf' (size roots');
      skFORS_eles' <- rcons skFORS_eles' skFORS_ele';
      leaves' <- rcons leaves' leaf';
      roots' <- rcons roots' root';
    }
    pkFORS' <- trco ps (set_kpidx (set_typeidx (set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx) trcotype) (get_kpidx (set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx)))
                    (flatten (map DigestBlock.val roots'));
    
    
    (* Additional checks *)
    (* 
      ITSR: 
      The adversary managed to find a message that, when signed, only uses secret key values that
      have already been revealed as part of signatures of different, previously signed messages 
    *)
    valid_ITSR <-    (forall idx, idx \in lidxs' => idx \in O_CMA_MFORSTWESNPRF_AV.lidxs) 
                  /\ ! (mk', m') \in zip O_CMA_MFORSTWESNPRF_AV.mks O_CMA_MFORSTWESNPRF.qs;
    
    (*
      OpenPRE (assuming no ITSR break):
      Even though the signed message uses a secret key value that was not yet revealed (i.e., no ITSR break),
      the adversary managed to find a value that maps to the same leaf as this original secret key value.  
    *)
    (dfidx, dftidx, dflfidx) <- nth witness lidxs' (find (fun i => ! i \in O_CMA_MFORSTWESNPRF_AV.lidxs) lidxs');
    (x', ap') <- nth witness (val sigFORSTW') dftidx;
    skFORSt <- nth witness (val (nth witness (nth witness sk.`1 tidx) kpidx)) dftidx;
    x <- nth witness skFORSt dflfidx;
    leaf' <- nth witness leaves' dftidx;
    leaf <- f ps (set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx) 0 (dftidx * t + dflfidx)) (val x);
    valid_OpenPRE <- leaf' = leaf;  
    
    (*
      Tree-hash TCR (assuming no ITSR and no OpenPRE breaks):
      Even though there is a leaf (computed from the secret key value) in the forged signature that does not match
      the corresponding original leaf, the adversary managed to find an authentication path that still results in the
      same root as the original tree's root (which requires a collision for the tree hash function). 
    *) 
    root' <- nth witness roots' dftidx; 
    leaves <- mkseq (fun (i : int) => f ps (set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx) 0 (dftidx * t + i)) (val (nth witness skFORSt i))) t;
    root <- val_bt_trh ps (set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx) (list2tree leaves) dflfidx;
    valid_TRHTCR <- root' = root;

    is_valid <- pkFORS' = pkFORS;
    
    is_fresh <- ! (m' \in O_CMA_MFORSTWESNPRF.qs);
    
    return is_valid /\ is_fresh; 
  }
}.

local equiv Eqv_EUF_CMA_MFORSTWESNPRF_C_V:
  EUF_CMA_MFORSTWESNPRF_C.main ~ EUF_CMA_MFORSTWESNPRF_V.main :
    ={glob A} ==> ={res}.
proof.
proc.
seq 5 5 : (   ={ad, ps, sk, pk, m', sig', O_CMA_MFORSTWESNPRF.qs}
           /\ pk{1}.`2 = ps{1}
           /\ pk{1}.`3 = ad{1}).
+ call (: ={glob O_CMA_MFORSTWESNPRF_AV}); 1: by sim.
  inline{1} 4; inline{1} 5; inline{2} 4; inline{2} 5.
  inline{1} 3; inline{2} 3.
  wp => />.
  while (#post).
  - wp => /=. 
    conseq (: _ ==> ={skFORSl, pkFORSl}) => //.
    by sim.
  by wp; rnd; wp; skip.
inline{1} 2; inline{1} 1; inline{1} 9; inline{1} 13.
swap{1} 24 17; swap{1} [21..22] 19; swap{1} 21 -20.
sp 1 0; wp 20 11.
conseq (: _ ==> ={pkFORS'} /\ pkFORS0{1} = pkFORS{2}) => //.
wp => /=.
while (   roots{1} = roots'{2}
       /\ ps2{1} = ps{2}
       /\ ad2{1} = set_kpidx (set_tidx (set_typeidx ad{2} trhtype) tidx{2}) kpidx{2}
       /\ sig1{1} = sigFORSTW'{2}
       /\ lidxs'{2} = g (m2{1}, idx{1})).
+ wp; skip => /> &1 &2 ltk_szrsp.
  have -> //:
    bs2int (rev (take a (drop (a * size roots'{2}) (val m2{1})))) 
    =
    (nth witness (g (m2{1}, idx{1})) (size roots'{2})).`3.
  rewrite /g /= nth_mkseq 2:/=; 1: smt(size_ge0).
  do 2! congr; rewrite /chunk nth_mkseq 2://.
  by rewrite size_ge0 valP /= mulzK 2://; 1: smt(ge1_a).
by wp; skip.
qed.


local clone import ExactIter as EI with
  type t <- dgstblock list,
  
  op c <- 1,
  op step <- 1
  
  proof *.
  realize c_gt0 by trivial.
  realize step_gt0 by trivial.


local module O_SMDTOpenPRE_Default_Init_LoopBody : AdvLoop = {
  import var O_SMDTOpenPRE_Default
  var tws : adrs list
  
  proc body(ys : dgstblock list, i : int) : dgstblock list = {
    var x : dgst;
    var y : dgstblock;
    var tw : adrs;
    var twy : adrs * dgstblock;
    
    tw <- nth witness tws i;
    x <$ ddgstblocklift;
    y <- f pp tw x;
    twy <- (tw, y);
    xs <- rcons xs x;
    ys <- rcons ys y;
    ts <- rcons ts twy;
    
    return ys;
  }
}.
  
local module O_SMDTOpenPRE_Default_Init_LoopBodyNest1 : AdvLoop = {
  import var O_SMDTOpenPRE_Default
  import var O_SMDTOpenPRE_Default_Init_LoopBody
  var i : int
   
  proc body(ys : dgstblock list, j : int) : dgstblock list = {
    var x : dgst;
    var y : dgstblock;
    var tw : adrs;
    var twy : adrs * dgstblock;
    
    tw <- nth witness tws (i * l * k * t + j);
    x <$ ddgstblocklift;
    y <- f pp tw x;
    twy <- (tw, y);
    xs <- rcons xs x;
    ys <- rcons ys y;
    ts <- rcons ts twy;
    
    return ys;
  }
}.

local module O_SMDTOpenPRE_Default_Init_LoopBodyNest2 : AdvLoop = {
  import var O_SMDTOpenPRE_Default
  import var O_SMDTOpenPRE_Default_Init_LoopBody
  import var O_SMDTOpenPRE_Default_Init_LoopBodyNest1
  var j : int
   
  proc body(ys : dgstblock list, u : int) : dgstblock list = {
    var x : dgst;
    var y : dgstblock;
    var tw : adrs;
    var twy : adrs * dgstblock;
    
    tw <- nth witness tws (i * l * k * t + j * k * t + u);
    x <$ ddgstblocklift;
    y <- f pp tw x;
    twy <- (tw, y);
    xs <- rcons xs x;
    ys <- rcons ys y;
    ts <- rcons ts twy;
    
    return ys;
  }
}.


local module O_SMDTOpenPRE_Default_Init_CL = {
  import var O_SMDTOpenPRE_Default
  import var O_SMDTOpenPRE_Default_Init_LoopBody
  import var O_SMDTOpenPRE_Default_Init_LoopBodyNest1
  import var O_SMDTOpenPRE_Default_Init_LoopBodyNest2
  
  proc init1(pp_init : pseed, tws_init : adrs list) : dgstblock list = {
    var x : dgst;
    var y : dgstblock;
    var ys : dgstblock list;
    var tw : adrs;
    var twy : adrs * dgstblock;
    
    tws <- tws_init;
    pp <- pp_init;
    ts <- [];
    xs <- [];
    os <- [];
    ys <- [];
    
    ys <@ Loop(O_SMDTOpenPRE_Default_Init_LoopBody).loop1(ys, d * k * t);
    
    return ys;
  }
  
  proc init2(pp_init : pseed, tws_init : adrs list) : dgstblock list = {
    var x : dgst;
    var y : dgstblock;
    var ys : dgstblock list;
    var tw : adrs;
    var twy : adrs * dgstblock;
    
    tws <- tws_init;
    pp <- pp_init;
    ts <- [];
    xs <- [];
    os <- [];
    ys <- [];
    
    i <- 0;
    while (i < s) {
      ys <@ Loop(O_SMDTOpenPRE_Default_Init_LoopBodyNest1).loop1(ys, l * k * t);
      i <- i + 1;
    }
    
    return ys;
  }
  
  proc init3(pp_init : pseed, tws_init : adrs list) : dgstblock list = {
    var x : dgst;
    var y : dgstblock;
    var ys : dgstblock list;
    var tw : adrs;
    var twy : adrs * dgstblock;
    
    tws <- tws_init;
    pp <- pp_init;
    ts <- [];
    xs <- [];
    os <- [];
    ys <- [];
    
    i <- 0;
    while (i < s) {
      j <- 0;
      while (j < l) {
        ys <@ Loop(O_SMDTOpenPRE_Default_Init_LoopBodyNest2).loop1(ys, k * t);
        j <- j + 1;
      }
      i <- i + 1;
    }
    
    return ys;
  }
}.

local equiv Eqv_O_SMDTOpenPRE_Default_Init_Orig_CL1:
  O_SMDTOpenPRE_Default.init ~ O_SMDTOpenPRE_Default_Init_CL.init1 :
    ={arg} /\ d * k * t <= size tws_init{1} ==> ={res, glob O_SMDTOpenPRE_Default}.
proof.
proc.
inline{2} 7.
wp => /=.
while (   ={glob O_SMDTOpenPRE_Default}
       /\ ys{1} = t{2} 
       /\ tws_init{1} = O_SMDTOpenPRE_Default_Init_LoopBody.tws{2}
       /\ n{2} = d * k * Top.t
       /\ d * k * Top.t <= size O_SMDTOpenPRE_Default_Init_LoopBody.tws{2} 
       /\ size O_SMDTOpenPRE_Default.ts{1} = i{2}
       /\ size O_SMDTOpenPRE_Default.ts{1} <= d * k * t).
+ inline{2} 1.
  by wp; rnd; wp; skip => />; smt(size_rcons).
by wp; skip => />; smt(ge1_d ge1_k ge2_t).
qed.

local equiv Eqv_O_SMDTOpenPRE_Default_Init_CL1_CL2:
  O_SMDTOpenPRE_Default_Init_CL.init1 ~ O_SMDTOpenPRE_Default_Init_CL.init2 :
    ={arg} ==> ={res, glob O_SMDTOpenPRE_Default}.
proof.
proc.
rewrite equiv [{1} 7 (loop1_loopk O_SMDTOpenPRE_Default_Init_LoopBody) (ys, s, l * k * t :@ ys)].
+ wp; skip => />; rewrite dval; smt(ge1_s Top.ge1_l ge1_k ge2_t). 
inline{1} 7.
wp => /=.
while (   ={glob O_SMDTOpenPRE_Default_Init_LoopBody}
       /\ i{1} = O_SMDTOpenPRE_Default_Init_LoopBodyNest1.i{2}
       /\ t{1} = ys{2} 
       /\ tws_init{1} = O_SMDTOpenPRE_Default_Init_LoopBody.tws{2}
       /\ n{1} = s
       /\ k{1} = l * Top.k * Top.t).
+ inline{2} 1.
  wp => /=.
  while (   ={glob O_SMDTOpenPRE_Default_Init_LoopBody, t}
         /\ j{1} = i{2}
         /\ i{1} = O_SMDTOpenPRE_Default_Init_LoopBodyNest1.i{2}
         /\ k{1} = n{2}
         /\ k{1} = l * Top.k * Top.t).
  - inline{1} 1; inline{2} 1.
    by wp; rnd; wp; skip => /> /#.
  by wp; skip => /> /#.
by wp; skip => /> /#.
qed.

local equiv Eqv_O_SMDTOpenPRE_Default_Init_CL2_CL3:
  O_SMDTOpenPRE_Default_Init_CL.init2 ~ O_SMDTOpenPRE_Default_Init_CL.init3 :
    ={arg} ==> ={res, glob O_SMDTOpenPRE_Default}.
proof.
proc.
while (={glob O_SMDTOpenPRE_Default_Init_LoopBodyNest1, ys}).
+ rewrite equiv [{1} 1 (loop1_loopk O_SMDTOpenPRE_Default_Init_LoopBodyNest1) (ys, l, k * t :@ ys)].
  - by wp; skip => />; smt(ge1_k ge2_t).
  inline{1} 1.
  wp => /=.
  while (   ={glob O_SMDTOpenPRE_Default_Init_LoopBodyNest1}
         /\ i{1} = O_SMDTOpenPRE_Default_Init_LoopBodyNest2.j{2}
         /\ k{1} = Top.k * Top.t
         /\ n{1} = l
         /\ t{1} = ys{2}).
  - inline{2} 1.
    wp => /=.
    while (   ={glob O_SMDTOpenPRE_Default_Init_LoopBodyNest1, t}
           /\ i{1} = O_SMDTOpenPRE_Default_Init_LoopBodyNest2.j{2}
           /\ k{1} = Top.k * Top.t
           /\ n{1} = l
           /\ j{1} = i{2}
           /\ n{2} = Top.k * Top.t).
    * inline{1} 1; inline{2} 1.
      wp; rnd; wp; skip => /> /#.
    by wp; skip.
  by wp; skip => /> /#.
by wp; skip => /> /#.
qed.

local module O_SMDTOpenPRE_Default_ILN = {
  import var O_SMDTOpenPRE_Default
  
  proc init(pp_init : pseed, tws_init : adrs list) : dgstblock list = {
    var x : dgst;
    var y : dgstblock;
    var ys : dgstblock list;
    var tw : adrs;
    var twy : adrs * dgstblock;
    var i, j, u, v : int;
    
    pp <- pp_init;
    ts <- [];
    xs <- [];
    os <- [];
    ys <- [];
    i <- 0;
    while (i < s) {
      j <- 0;
      while (j < l) {
        u <- 0;
        while (u < k) {
          v <- 0;
          while (v < t) {
            tw <- nth witness tws_init (i * k * l * t + j * k * t + u * t + v);
            x <$ ddgstblocklift;
            y <- f pp tw x;
            twy <- (tw, y);
            xs <- rcons xs x;
            ys <- rcons ys y;
            ts <- rcons ts twy;
            v <- v + 1;
          }
          u <- u + 1;
        }
        j <- j + 1;
      }
      i <- i + 1;
    }
    
    return ys;
  }
}.

local equiv Eqv_O_SMDTOpenPRE_Default_Init_CL3_ILN:
  O_SMDTOpenPRE_Default_Init_CL.init3 ~ O_SMDTOpenPRE_Default_ILN.init :
    ={arg} ==> ={res, glob O_SMDTOpenPRE_Default}.
proof.
proc.
while (   ={glob O_SMDTOpenPRE_Default, ys}
       /\ O_SMDTOpenPRE_Default_Init_LoopBodyNest1.i{1} = i{2}
       /\ O_SMDTOpenPRE_Default_Init_LoopBody.tws{1} = tws_init{2}).
+ wp => /=.
  while (   #pre
         /\ O_SMDTOpenPRE_Default_Init_LoopBodyNest2.j{1} = j{2}).
  - rewrite equiv [{1} 1 (loop1_loopk O_SMDTOpenPRE_Default_Init_LoopBodyNest2) (ys, k, t :@ ys)].
    * by wp; skip => />; smt(ge2_t).
    inline{1} 1.
    wp => /=.
    while (   ={glob O_SMDTOpenPRE_Default}
           /\ O_SMDTOpenPRE_Default_Init_LoopBody.tws{1} = tws_init{2}
           /\ O_SMDTOpenPRE_Default_Init_LoopBodyNest1.i{1} = i{2}
           /\ O_SMDTOpenPRE_Default_Init_LoopBodyNest2.j{1} = j{2}
           /\ i{1} = u{2}
           /\ t{1} = ys{2}
           /\ n{1} = Top.k
           /\ k{1} = Top.t).
    * wp => /=.
      while (   #pre
             /\ j{1} = v{2}).
      + inline{1} 1.
        by wp; rnd; wp; skip => /> /#.
      by wp; skip => /> /#.
    by wp; skip => /> /#.
  by wp; skip => /> /#. 
by wp; skip => /> /#.
qed.

local equiv Eqv_O_SMDTOpenPRE_Default_Init_Orig_ILN:
  O_SMDTOpenPRE_Default.init ~ O_SMDTOpenPRE_Default_ILN.init :
    ={arg} /\ d * k * t <= size tws_init{1} ==> ={res, glob O_SMDTOpenPRE_Default}.
proof.
transitivity O_SMDTOpenPRE_Default_Init_CL.init1
             (={arg} /\ d * k * t <= size tws_init{1} ==> ={res, glob O_SMDTOpenPRE_Default})
             (={arg} ==> ={res, glob O_SMDTOpenPRE_Default}) => [/# | // | |].
+ by apply Eqv_O_SMDTOpenPRE_Default_Init_Orig_CL1.
transitivity O_SMDTOpenPRE_Default_Init_CL.init2
             (={arg} ==> ={res, glob O_SMDTOpenPRE_Default})
             (={arg} ==> ={res, glob O_SMDTOpenPRE_Default}) => [/# | // | |].
+ by apply Eqv_O_SMDTOpenPRE_Default_Init_CL1_CL2.
transitivity O_SMDTOpenPRE_Default_Init_CL.init3
             (={arg} ==> ={res, glob O_SMDTOpenPRE_Default})
             (={arg} ==> ={res, glob O_SMDTOpenPRE_Default}) => [/# | // | |].
+ by apply Eqv_O_SMDTOpenPRE_Default_Init_CL2_CL3.
by apply Eqv_O_SMDTOpenPRE_Default_Init_CL3_ILN.
qed.

(*
local lemma EUFCMA_MFORSTWESNPRF_OPRE &m:
  Pr[EUF_CMA_MFORSTWESNPRF(A, O_CMA_MFORSTWESNPRF).main() @ &m : res] 
  <= 
  Pr[MCO_ITSR.ITSR(R_EUFCMA_ITSR(A), MCO_ITSR.O_ITSR_Default).main() @ &m : res]
  +
  Pr[FC_OpenPRE.SM_DT_OpenPRE_C(R_FSMDTOpenPREC_EUFCMA(A), FC_OpenPRE.O_SMDTOpenPRE_Default, FC.O_THFC_Default).main() @ &m : res]
  +
  Pr[FC_TCR.SM_DT_TCR_C(R_FSMDTTCRC_EUFCMA(A), FC_TCR.O_SMDTTCR_Default, FC.O_THFC_Default).main() @ &m : res]
  + 
  Pr[TRHC_TCR.SM_DT_TCR_C(R_TRHSMDTTCRC_EUFCMA(A), TRHC_TCR.O_SMDTTCR_Default, TRHC.O_THFC_Default).main() @ &m : res]
  +
  Pr[TRCOC_TCR.SM_DT_TCR_C(R_TRCOSMDTTCRC_EUFCMA(A), TRCOC_TCR.O_SMDTTCR_Default, TRCOC.O_THFC_Default).main() @ &m : res].
proof.
admit.
qed.
*)
local lemma EUFCMA_MFORSTWESNPRF_OPRE &m:
  Pr[EUF_CMA_MFORSTWESNPRF(A, O_CMA_MFORSTWESNPRF).main() @ &m : res] 
  <= 
  Pr[MCO_ITSR.ITSR(R_ITSR_EUFCMA(A), MCO_ITSR.O_ITSR_Default).main() @ &m : res]
  +
  Pr[F_OpenPRE.SM_DT_OpenPRE(R_FSMDTOpenPRE_EUFCMA(A), F_OpenPRE.O_SMDTOpenPRE_Default).main() @ &m : res]
(*
  +  
  Pr[FC_TCR.SM_DT_TCR_C(R_FSMDTTCRC_EUFCMA(A), FC_TCR.O_SMDTTCR_Default, FC.O_THFC_Default).main() @ &m : res]
*)
  + 
  Pr[TRHC_TCR.SM_DT_TCR_C(R_TRHSMDTTCRC_EUFCMA(A), TRHC_TCR.O_SMDTTCR_Default, TRHC.O_THFC_Default).main() @ &m : res]
  +
  Pr[TRCOC_TCR.SM_DT_TCR_C(R_TRCOSMDTTCRC_EUFCMA(A), TRCOC_TCR.O_SMDTTCR_Default, TRCOC.O_THFC_Default).main() @ &m : res].
proof.
have ->:
  Pr[EUF_CMA_MFORSTWESNPRF(A, O_CMA_MFORSTWESNPRF).main() @ &m : res]
  =
  Pr[EUF_CMA_MFORSTWESNPRF_V.main() @ &m : res].
+ byequiv => //.
  transitivity EUF_CMA_MFORSTWESNPRF_C.main (={glob A} ==> ={res}) (={glob A} ==> ={res}) => [/# | // | |].
  - by apply Eqv_EUF_CMA_MFORSTWESNPRF_Orig_C.
  by apply Eqv_EUF_CMA_MFORSTWESNPRF_C_V.
rewrite -!RField.addrA.
rewrite Pr[mu_split EUF_CMA_MFORSTWESNPRF_V.valid_ITSR] StdOrder.RealOrder.ler_add.
+ byequiv => //.
  proc.
  inline{2} 2; inline{2} 1.
  seq 5 7 : (   ={pk, sk, m', sig'}
             /\ ad{1} = R_ITSR_EUFCMA.ad{2}
             /\ ps{1} = R_ITSR_EUFCMA.ps{2}
             /\ O_ITSR_Default.ts{2} = zip O_CMA_MFORSTWESNPRF_AV.mks{1} O_CMA_MFORSTWESNPRF.qs{1}
             /\ O_CMA_MFORSTWESNPRF_AV.lidxs{1} 
                = 
                flatten (map (fun (mkm : mkey * msg) => g (mco mkm.`1 mkm.`2)) 
                             (zip O_CMA_MFORSTWESNPRF_AV.mks{1} O_CMA_MFORSTWESNPRF.qs{1}))).
  - call (:   ={mmap}(O_CMA_MFORSTWESNPRF, R_ITSR_EUFCMA)
           /\ O_CMA_MFORSTWESNPRF.sk{1} = (R_ITSR_EUFCMA.skFORSs, R_ITSR_EUFCMA.ps, R_ITSR_EUFCMA.ad){2}
           /\ O_ITSR_Default.ts{2} = zip O_CMA_MFORSTWESNPRF_AV.mks{1} O_CMA_MFORSTWESNPRF.qs{1}
           /\ O_CMA_MFORSTWESNPRF_AV.lidxs{1}
              =
              flatten (map (fun (mkm : mkey * msg) => g (mco mkm.`1 mkm.`2)) 
                           (zip O_CMA_MFORSTWESNPRF_AV.mks{1} O_CMA_MFORSTWESNPRF.qs{1}))
           /\ size O_CMA_MFORSTWESNPRF_AV.mks{1} = size O_CMA_MFORSTWESNPRF.qs{1}).
    * proc; inline *.
      sp 1 0.
      if => //.
      + wp => />.
        while (   ={sig, m0, skFORS0}
               /\ ps0{1} = ps{2}
               /\ ad0{1} = ad{2}).
        - wp 10 10 => /=.
          sp 7 7.
          conseq (: _ ==> ={sig, leaves}) => //.
          by sim.
        wp; rnd; wp; skip => /> &1 &2 eqszmkss ninm mk mkin sig /lezNgt gek_szsig _.
        by rewrite zip_rcons 1:// /= map_rcons flatten_rcons ?size_rcons eqszmkss.
      wp => /=.
      conseq (: _ ==> ={mk, sig}) => //.
      by sim.
    inline{1} 4; inline{1} 5.
    wp => /=.
    seq 2 3 : (   #pre 
               /\ ad{1} = adz 
               /\ ad{1} = R_ITSR_EUFCMA.ad{2} 
               /\ ps{1} = R_ITSR_EUFCMA.ps{2}
               /\ O_ITSR_Default.ts{2} = []).
    * by rnd; wp; skip. 
    inline{1} 1; inline{2} 1.
    sp 2 2; wp => />.
    by sim.
  inline{2} 4.
  conseq (: _ ==> EUF_CMA_MFORSTWESNPRF_V.valid_ITSR{1} 
                  => 
                     (forall (x0 : int * int * int), x0 \in ikssl_f{2} => x0 \in ikssl_q{2}) 
                  /\ ! ((k{2}, x{2}) \in kxl{2})) => //.
  swap{1} [2..3] -1; swap{1} 6 -3; sp 3 0.
  wp => /=.
  conseq (: _ ==> true) => [/> |].
  progress. rewrite H0 H H2.
  while{1} (true) (Top.k - size roots'{1}).
  + move=> _ z.
    by wp; skip => />; smt(size_rcons).
  by wp; skip => /> /#.
rewrite Pr[mu_split EUF_CMA_MFORSTWESNPRF_V.valid_OpenPRE] StdOrder.RealOrder.ler_add.
+ byequiv=> //.
  proc.
  rewrite equiv [{2} 3 Eqv_O_SMDTOpenPRE_Default_Init_Orig_ILN]; last first.
  - inline{1} 2; inline{2} 2.
    wp => />.
    while (   ={tidx, adl, pp, R_FSMDTOpenPRE_EUFCMA.ad}
            /\ size adl{1} = tidx{1} * l * k * t
            /\ 0 <= tidx{1} <= s).
    * wp => /=.
      while (   ={tidx, kpidx, adl, pp, R_FSMDTOpenPRE_EUFCMA.ad}
             /\ size adl{1} = tidx{1} * l * k * t + kpidx{1} * k * t
             /\ 0 <= tidx{1} < s
             /\ 0 <= kpidx{1} <= l).
      + wp => /=.
        while (   ={tidx, kpidx, tbidx, adl, pp, R_FSMDTOpenPRE_EUFCMA.ad}
               /\ size adl{1} = tidx{1} * l * k * t + kpidx{1} * k * t + tbidx{1}
               /\ 0 <= tidx{1} < s
               /\ 0 <= kpidx{1} < l
               /\ 0 <= tbidx{1} <= k * t).
        - by wp; skip => />; smt(size_rcons).
        by wp; skip => />; smt(ge1_k ge2_t).      
      by wp; skip => />; smt(Top.ge1_l ge1_k ge2_t).
    by wp; rnd; skip => />; smt(dval ge1_s Top.ge1_l ge1_k ge2_t).
  inline{1} 3; inline{2} 2; inline{2} 7.
  inline{2} 17.
  seq 7 24 : (   ={glob A}
              /\ ad{1} = adz
              /\ ad{1} = R_FSMDTOpenPRE_EUFCMA.ad{2}
              /\ ad{1} = ad0{1}
              /\ ps{1} = pp{2}
              /\ ps{1} = ps0{1}
              /\ pp{2} = O_SMDTOpenPRE_Default.pp{2}
              /\ pp{2} = R_FSMDTOpenPRE_EUFCMA.ps{2}
              /\ O_SMDTOpenPRE_Default.os{2} = []
              /\ R_FSMDTOpenPRE_EUFCMA.lidxs{2} = []
              /\ R_FSMDTOpenPRE_EUFCMA.mmap{2} = empty
              /\ R_FSMDTOpenPRE_EUFCMA.leavess{2} = unzip2 O_SMDTOpenPRE_Default.ts{2}
              /\ pkFORSs0{1} = pkFORSs{2}
              /\ (forall (i j u v : int), 0 <= i < s => 0 <= j < l => 0 <= u < k => 0 <= v < t =>
                    nth witness O_SMDTOpenPRE_Default.xs{2} (i * l * k * t + j * k * t + u * t + v)
                    =
                    val (nth witness (nth witness (val (nth witness (nth witness skFORSs0{1} i) j)) u) v))
              /\ (forall (i j u v : int), 0 <= i < s => 0 <= j < l => 0 <= u < k => 0 <= v < t =>
                    nth witness O_SMDTOpenPRE_Default.ts{2} (i * l * k * t + j * k * t + u * t + v)
                    =
                    (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) i) j) 0 (u * t + v),
                     f O_SMDTOpenPRE_Default.pp{2} (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) i) j) 0 (u * t + v))
                       (nth witness O_SMDTOpenPRE_Default.xs{2} (i * l * k * t + j * k * t + u * t + v))))
              /\ size O_SMDTOpenPRE_Default.ts{2} = d * k * t
              /\ size O_SMDTOpenPRE_Default.xs{2} = size O_SMDTOpenPRE_Default.ts{2}).
  - while{2} (forall (i j : int), 0 <= i < size pkFORSs{2} => 0 <= j < l =>
                nth witness (nth witness pkFORSs{2} i) j
                =
                let rs = mkseq (fun (u : int) =>
                            val_bt_trh R_FSMDTOpenPRE_EUFCMA.ps{2} (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trcotype) i) j) 
                                       (list2tree (take t (drop (i * l * k * t + j * k * t + u * t) R_FSMDTOpenPRE_EUFCMA.leavess{2}))) i) k in
                  trco R_FSMDTOpenPRE_EUFCMA.ps{2} (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trcotype) i) j)
                       (flatten (map DigestBlock.val rs)))
             (s - size pkFORSs{2}).
    * admit.
    admit.
  (*
    wp => /=.
    while (   ps0{1} = O_SMDTOpenPRE_Default.pp{2}
           /\ ad0{1} = R_FSMDTOpenPRE_EUFCMA.ad{2}
           /\ (forall (i j u v : int), 0 <= i < s => 0 <= j < l => 0 <= u < k => 0 <= v < t =>
                nth witness tws_init{2} (i * l * k * t + j * k * t + u * t + v)
                =
                set_thtbidx (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) i) j) 0 (u * t + v))
           /\ (forall (i j u v : int), 0 <= i < size skFORSs0{1} => 0 <= j < l => 0 <= u < k => 0 <= v < t =>
                nth witness O_SMDTOpenPRE_Default.xs{2} (i * l * k * t + j * k * t + u * t + v)
                =
                val (nth witness (nth witness (val (nth witness (nth witness skFORSs0{1} i) j)) u) v))
           /\ (forall (i j u v : int), 0 <= i < size skFORSs0{1} => 0 <= j < l => 0 <= u < k => 0 <= v < t =>
                 nth witness O_SMDTOpenPRE_Default.ts{2} (i * l * k * t + j * k * t + u * t + v)
                 =
                 (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) i) j) 0 (u * t + v),
                  f O_SMDTOpenPRE_Default.pp{2} (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) i) j) 0 (u * t + v))
                    (nth witness O_SMDTOpenPRE_Default.xs{2} (i * l * k * t + j * k * t + u * t + v))))
           /\ size skFORSs0{1} <= s
           /\ size O_SMDTOpenPRE_Default.ts{2} <= d * k * t
           /\ size O_SMDTOpenPRE_Default.xs{2} = size O_SMDTOpenPRE_Default.ts{2}).
    admit.
  *)
  inline{2} 13; inline{2} 12; inline{2} 11.
  wp 30 10 => /=.
  conseq (: _ 
            ==> 
               is_fresh{1} 
            /\ !EUF_CMA_MFORSTWESNPRF_V.valid_ITSR{1} 
            /\ EUF_CMA_MFORSTWESNPRF_V.valid_OpenPRE{1} 
            =>
               ! (i{2} \in O_SMDTOpenPRE_Default.os{2})
            /\ f pp{2} tw{2} x{2} = y{2}).
  * 
  (*
    progress.
    rewrite size_ge0. smt().
    smt().
    rewrite nth_uniq => i j.
    rewrite size_map H1 => rng_i rng_j neqi_j.
    rewrite 2?(nth_map witness) 1,2:H1 1,2:// /=.
    print edivzP.
    print divz_eq.
    move: neqi_j.
    rewrite (divz_eq i (l * k * t)) (divz_eq j (l * k * t)) => neqi_j.
    rewrite (divz_eq (i %% (l * k * t)) (k * t)).
    rewrite modz_dvd 1:-mulrA 1:dvdz_mull 1:dvdzz.
    rewrite (divz_eq (i %% (k * t)) t).
    rewrite modz_dvd 1:dvdz_mull 1:dvdzz.
    move: (H0 (i %/ (l * k * t)) (i %% (l * k * t) %/ (k * t)) 
              (i %% (k * t) %/ t) (i %% t) _ _ _ _).
    admit.
    admit.
    admit.
    rewrite modz_ge0 2:ltz_pmod 3://; 1,2: smt(ge2_t).
    rewrite ?addrA ?mulrA => -> /=.
    rewrite (divz_eq (j %% (l * k * t)) (k * t)).
    rewrite modz_dvd 1:-mulrA 1:dvdz_mull 1:dvdzz.
    rewrite (divz_eq (j %% (k * t)) t).
    rewrite modz_dvd 1:dvdz_mull 1:dvdzz.
    move: (H0 (j %/ (l * k * t)) (j %% (l * k * t) %/ (k * t)) 
              (j %% (k * t) %/ t) (j %% t) _ _ _ _).
    admit.
    admit.
    admit.
    rewrite modz_ge0 2:ltz_pmod 3://; 1,2: smt(ge2_t).
    rewrite ?addrA ?mulrA => -> /=.
    rewrite -eq_adrs_idxsq negb_forall /=.
    case (i %/ (l * k * t) <> j %/ (l * k * t)) => [n1 | /= n2].
    exists 4. rewrite /eq_idx. admit.
    have neq2: i %% (l * k * t) <> j %% (l * k * t) by smt().
    rewrite (divz_eq (i %% (l * k * t)) (k * t)) (divz_eq (j %% (l * k * t)) (k * t)) in neq2.
    rewrite modz_dvd in neq2. rewrite -mulrA dvdz_mull 1:dvdzz //.
    rewrite modz_dvd in neq2. rewrite -mulrA dvdz_mull 1:dvdzz //.
    
    case (i %% (l * k * t) %/ (k * t) <> j %% (l * k * t) %/ (k * t)) => [nn1 | /= nn2].
    exists 2. admit.
    have nneq2: i %% (k * t) <> j %% (k * t) by smt().
    print valid_tidx.
    admit.
    smt().
  *)
    admit.
  inline{2} 10.
  wp => /=.
  while{1} (   leaves'{1} 
               =
               mkseq (fun (i : int) => 
                         f ps{1} (set_thtbidx (set_kpidx (set_tidx (set_typeidx ad{1} trhtype) tidx{1}) kpidx{1}) 0 (i * t + (nth witness lidxs'{1} i).`3)) (val (nth witness (val sigFORSTW'{1}) i).`1)) (size roots'{1})
            /\ size roots'{1} = size skFORS_eles'{1}
            /\ size roots'{1} = size leaves'{1}
            /\ size roots'{1} <= k)
           (k - size roots'{1}).
  - move=> _ z.
    wp; skip => />.
    progress. rewrite size_rcons mkseqS 1:size_ge0 //.
    smt(size_rcons). 
    smt(size_rcons).
    smt(size_rcons).
    smt(size_rcons).
  wp => /=.
  call (:   O_CMA_MFORSTWESNPRF.sk{1}.`2 = R_FSMDTOpenPRE_EUFCMA.ps{2}
         /\ O_CMA_MFORSTWESNPRF.sk{1}.`3 = R_FSMDTOpenPRE_EUFCMA.ad{2}
         /\ O_SMDTOpenPRE_Default.pp{2} = R_FSMDTOpenPRE_EUFCMA.ps{2}
         /\ ={mmap}(O_CMA_MFORSTWESNPRF, R_FSMDTOpenPRE_EUFCMA)
         /\ ={lidxs}(O_CMA_MFORSTWESNPRF_AV, R_FSMDTOpenPRE_EUFCMA)
         /\ dom O_CMA_MFORSTWESNPRF.mmap{1} = mem O_CMA_MFORSTWESNPRF.qs{1}
         /\ (forall (i j u v : int), 0 <= i < s => 0 <= j < l => 0 <= u < k => 0 <= v < t =>
                nth witness R_FSMDTOpenPRE_EUFCMA.leavess{2} (i * l * k * t + j * k * t + u * t + v)
                =
                f O_SMDTOpenPRE_Default.pp{2} (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) i) j) 0 (u * t + v))
                  (nth witness O_SMDTOpenPRE_Default.xs{2} (i * l * k * t + j * k * t + u * t + v)))
         /\ (forall (i j u v : int), 0 <= i < s => 0 <= j < l => 0 <= u < k => 0 <= v < t =>
              nth witness O_SMDTOpenPRE_Default.xs{2} (i * l * k * t + j * k * t + u * t + v)
              =
              val (nth witness (nth witness (val (nth witness (nth witness O_CMA_MFORSTWESNPRF.sk{1}.`1 i) j)) u) v))
         /\ (forall (m : msg),
              m \in R_FSMDTOpenPRE_EUFCMA.mmap{2}
              =>
              all (mem R_FSMDTOpenPRE_EUFCMA.lidxs{2}) (g (mco (oget R_FSMDTOpenPRE_EUFCMA.mmap{2}.[m]) m)))
         /\ (forall (idxs : int * int * int),
              idxs \in R_FSMDTOpenPRE_EUFCMA.lidxs{2}
              <=>
              idxs.`1 %/ l * l * k * t +
              idxs.`1 %% l * k * t +
              idxs.`2 * t +
              idxs.`3 \in
              O_SMDTOpenPRE_Default.os{2})
         /\ size R_FSMDTOpenPRE_EUFCMA.leavess{2} = d * k * t).
  - proc.
    inline{1} 7.
    wp; sp 1 0 => /=.
    if => //.
    * while (   ={tidx, kpidx, idx}
             /\ O_SMDTOpenPRE_Default.pp{2} = R_FSMDTOpenPRE_EUFCMA.ps{2}
             /\ m{2} \in R_FSMDTOpenPRE_EUFCMA.mmap{2}
             /\ (cm, idx){2} = mco (oget R_FSMDTOpenPRE_EUFCMA.mmap{2}.[m{2}]) m{2}
             /\ tidx{2} = val idx{2} %/ l
             /\ kpidx{2} = val idx{2} %% l
             /\ sig{1} = sigFORSTW{2}
             /\ m0{1} = cm{2}
             /\ ps0{1} = R_FSMDTOpenPRE_EUFCMA.ps{2}
             /\ ad0{1} = set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) tidx{2}) kpidx{2}
             /\ skFORS0{1} = nth witness (nth witness skFORSs{1} tidx{1}) kpidx{1}
             /\ (forall (i j u v : int), 0 <= i < s => 0 <= j < l => 0 <= u < k => 0 <= v < t =>
                  nth witness R_FSMDTOpenPRE_EUFCMA.leavess{2} (i * l * k * t + j * k * t + u * t + v)
                  =
                  f O_SMDTOpenPRE_Default.pp{2} (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) i) j) 0 (u * t + v))
                    (nth witness O_SMDTOpenPRE_Default.xs{2} (i * l * k * t + j * k * t + u * t + v)))
             /\ (forall (i j u v : int),
                   0 <= i && i < s =>
                   0 <= j && j < l =>
                   0 <= u && u < k =>
                   0 <= v && v < t =>
                   nth witness O_SMDTOpenPRE_Default.xs{2} (i * l * k * t + j * k * t + u * t + v) 
                   =
                   val (nth witness (nth witness (val (nth witness (nth witness skFORSs{1} i) j)) u) v))
             /\ (forall (m : msg),
                  m \in R_FSMDTOpenPRE_EUFCMA.mmap{2}
                  =>
                  all (mem R_FSMDTOpenPRE_EUFCMA.lidxs{2}) (g (mco (oget R_FSMDTOpenPRE_EUFCMA.mmap{2}.[m]) m)))
             /\ (forall (idxs : int * int * int),
                  idxs \in R_FSMDTOpenPRE_EUFCMA.lidxs{2}
                  <=>
                  (idxs.`1 %/ l * l * k * t +
                  idxs.`1 %% l * k * t +
                  idxs.`2 * t +
                  idxs.`3 \in
                  O_SMDTOpenPRE_Default.os{2}
                  \/ 
                  idxs \in drop (size sigFORSTW{2}) (g (mco (oget R_FSMDTOpenPRE_EUFCMA.mmap{2}.[m{2}]) m{2}))))
             /\ size R_FSMDTOpenPRE_EUFCMA.leavess{2} = d * k * t
             /\ size sig{1} <= k).
      + inline{1} 4; inline{2} 3.
        wp => /=.
        while{1} (   leaves0{1} 
                     = 
                     mkseq (fun (i : int) =>
                             f ps1{1} (set_thtbidx ad1{1} 0 (idxt{1} * t + i)) (val (nth witness (nth witness (val skFORS1{1}) idxt{1}) i))) (size leaves0{1})
                  /\ size leaves0{1} <= t)
                 (t - size leaves0{1}).
        - move=> _ z.
          wp; skip => />.
          progress. rewrite size_rcons mkseqS 1:size_ge0 /=.
          by rewrite {1}H; congr.
          smt(size_rcons). smt(size_rcons).
        wp; skip => />.
        progress.
        rewrite mkseq0 //.
        smt(ge2_t).
        smt(ge2_t).
        congr.
        rewrite H2; 1..4: admit. rewrite valKd /=.
        congr. rewrite H9. congr.
        rewrite &(eq_from_nth witness).
        rewrite size_mkseq size_take; 1:smt(ge2_t).
        rewrite size_drop. admit. admit.
        move => i [ge0_i]; rewrite size_mkseq (: size leaves0_L = t) 1:/# => ltt_i.
        rewrite nth_mkseq 2:nth_take; 1..3: smt(ge2_t).
        print nth_drop.
        rewrite nth_drop; 1: admit. trivial. simplify.
        rewrite H1; 1..4: admit.
        rewrite H2; 1..4: admit.
        congr.
        trivial.
        rewrite size_rcons.
        move: H11. rewrite H4.
        rewrite mem_rcons /=.
        case => [-> // |].
        search rcons nth.
        search take drop.
        rewrite -(cat_take_drop (0 + 1) (drop _ _)) (take_nth witness) 1:size_drop 1:size_ge0 /= 1:/g /= 1:size_mkseq 1:/#.
        rewrite take0 /= drop_drop 1:// 1:size_ge0 (addrC 1).
        case => [idxval /=| -> //].
        left; left.
        move: idxval; rewrite nth_drop 1:size_ge0 1:// /=.
        rewrite /g /= nth_mkseq 1:size_ge0 1:// /=.
        move=> -> /=.
        congr.
        by move: H0 => <- /=.
        congr; congr.
        rewrite /chunk nth_mkseq 1:valP 1:size_ge0 1://.
        rewrite mulzK 2:/#; smt(ge1_a).
        simplify.
        by move: H0 => <- /=.
        move: H11; rewrite size_rcons mem_rcons /=.
        rewrite H4.
        case => [| idxind1]; last first.
        right. move: idxind1. 
        print drop_nth.
        rewrite (drop_nth witness (size sigFORSTW{2})) 1:size_ge0 1:/g 1:/= 1:size_mkseq; 1: smt(ge1_k).
        by simplify => ->.
        case => [| -> //].
        rewrite (drop_nth witness (size sigFORSTW{2})) 1:size_ge0 1:/g 1:/= 1:size_mkseq; 1: smt(ge1_k).
        simplify.
        rewrite /g /= nth_mkseq 1:size_ge0 1:// /=.
        move: H0 => <- /= idxssval; right; left.
        move: idxssval. apply contraLR. case (idxs) => x y z /=. admit.
        smt(size_rcons).
        smt(size_rcons).
        smt(size_rcons).
      wp; rnd; skip => />.
      progress.
      rewrite mem_set //.
      smt().
      rewrite allP => idxs.
      rewrite mem_cat /= {1}/g /= mkseqP => -[i] [rng_i /=].
      case (m1 = m{2}) => [eqmm | neqmm].
      rewrite eqmm get_set_sameE oget_some /= => ->; right.
      rewrite /g /= mkseqP; exists i => //.
      rewrite get_setE neqmm /= => validxs.
      move: (H2 m1 _). move: H7. rewrite mem_set neqmm //.
      rewrite allP => /(_ idxs _) //.
      rewrite validxs /g /= mkseqP; exists i => //.
      by move=> -> //. 
      move: H7. rewrite mem_cat drop0. rewrite H3 get_set_sameE oget_some //.
      move: H7. rewrite mem_cat drop0. rewrite H3 get_set_sameE oget_some //.
      smt(ge1_k).
      move: H. rewrite ?fun_ext => + x => /(_ x). 
      rewrite mem_set mem_rcons => -> /#.
      move/iffLR: (H12 idxs) => /(_ H14) /=.
      rewrite (: size sigFORSTW_R = size (g (mco (oget R_FSMDTOpenPRE_EUFCMA.mmap{2}.[m{2} <- mkL].[m{2}]) m{2}))).
      + rewrite (: size sigFORSTW_R = k) 1:/#.
        by rewrite /g /= size_mkseq; 1: smt(ge1_k).
      by rewrite drop_size.
      move/iffRL: (H12 idxs).
      rewrite (: size sigFORSTW_R = size (g (mco (oget R_FSMDTOpenPRE_EUFCMA.mmap{2}.[m{2} <- mkL].[m{2}]) m{2}))).
      + rewrite (: size sigFORSTW_R = k) 1:/#.
        by rewrite /g /= size_mkseq; 1: smt(ge1_k).
      by rewrite drop_size /= => /(_ H14).
    while (   ={tidx, kpidx, idx}
           /\ O_SMDTOpenPRE_Default.pp{2} = R_FSMDTOpenPRE_EUFCMA.ps{2}
           /\ m{2} \in R_FSMDTOpenPRE_EUFCMA.mmap{2}
           /\ (cm, idx){2} = mco (oget R_FSMDTOpenPRE_EUFCMA.mmap{2}.[m{2}]) m{2}
           /\ tidx{2} = val idx{2} %/ l
           /\ kpidx{2} = val idx{2} %% l
           /\ sig{1} = sigFORSTW{2}
           /\ m0{1} = cm{2}
           /\ ps0{1} = R_FSMDTOpenPRE_EUFCMA.ps{2}
           /\ ad0{1} = set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) tidx{2}) kpidx{2}
           /\ skFORS0{1} = nth witness (nth witness skFORSs{1} tidx{1}) kpidx{1}
           /\ (forall (i j u v : int), 0 <= i < s => 0 <= j < l => 0 <= u < k => 0 <= v < t =>
                nth witness R_FSMDTOpenPRE_EUFCMA.leavess{2} (i * l * k * t + j * k * t + u * t + v)
                =
                f O_SMDTOpenPRE_Default.pp{2} (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) i) j) 0 (u * t + v))
                  (nth witness O_SMDTOpenPRE_Default.xs{2} (i * l * k * t + j * k * t + u * t + v)))
           /\ (forall (i j u v : int),
                 0 <= i && i < s =>
                 0 <= j && j < l =>
                 0 <= u && u < k =>
                 0 <= v && v < t =>
                 nth witness O_SMDTOpenPRE_Default.xs{2} (i * l * k * t + j * k * t + u * t + v) 
                 =
                 val (nth witness (nth witness (val (nth witness (nth witness skFORSs{1} i) j)) u) v))
           /\ (forall (m : msg),
              m \in R_FSMDTOpenPRE_EUFCMA.mmap{2}
              =>
              all (mem R_FSMDTOpenPRE_EUFCMA.lidxs{2}) (g (mco (oget R_FSMDTOpenPRE_EUFCMA.mmap{2}.[m]) m)))
           /\ (forall (idxs : int * int * int),
              idxs \in R_FSMDTOpenPRE_EUFCMA.lidxs{2}
              <=>
              idxs.`1 %/ l * l * k * t +
              idxs.`1 %% l * k * t +
              idxs.`2 * t +
              idxs.`3 \in
              O_SMDTOpenPRE_Default.os{2})
           /\ size R_FSMDTOpenPRE_EUFCMA.leavess{2} = d * k * t
           /\ size sig{1} <= k).
    * inline{1} 4; inline{2} 3.
      wp => /=.
      while{1} (   leaves0{1} 
                   = 
                   mkseq (fun (i : int) =>
                           f ps1{1} (set_thtbidx ad1{1} 0 (idxt{1} * t + i)) (val (nth witness (nth witness (val skFORS1{1}) idxt{1}) i))) (size leaves0{1})
                /\ size leaves0{1} <= t)
               (t - size leaves0{1}).
      + move=> _ z.
        wp; skip => />.
        progress. rewrite size_rcons mkseqS 1:size_ge0 /=.
        by rewrite {1}H; congr.
        smt(size_rcons). smt(size_rcons).
      wp; skip => />.
      progress.
      by rewrite mkseq0.
      smt(ge2_t).
      smt(ge2_t).
      congr.
      rewrite H2; 1..4: admit. rewrite valKd /=.
      congr. rewrite H9. congr.
      rewrite &(eq_from_nth witness).
      rewrite size_mkseq size_take; 1:smt(ge2_t).
      rewrite size_drop. admit. admit.
      move => i [ge0_i]; rewrite size_mkseq (: size leaves0_L = t) 1:/# => ltt_i.
      rewrite nth_mkseq 2:nth_take; 1..3: smt(ge2_t).
      print nth_drop.
      rewrite nth_drop; 1: admit. trivial. simplify.
      rewrite H1; 1..4: admit.
      rewrite H2; 1..4: admit.
      congr.
      trivial.
      rewrite mem_rcons /=; right. smt().
      move: H11; rewrite mem_rcons /=.
      case => [idxssval | ].
      move/allP: (H3 m{2} H) => /(_ idxs).
      rewrite H4.
      rewrite -H0 /g /= mkseqP /= idxssval. apply. exists (size sigFORSTW{2}).
      split; 1: smt(size_ge0).
      move: idxssval. apply contraLR. case (idxs) =>  a b c /=. admit.
      smt().
      smt(size_rcons).
      smt(size_rcons).
      smt(size_rcons).
    by wp; skip => />; smt(ge1_k).
  inline{1} 4; inline{1} 5.
  wp; skip => /> &1 &2 nthxs nthts szts eqsztsxs.
  split => [| eqdm0 _ _ _ sig qs mks lidxs mmap os eqdm mmaplidxsrel lidxsdef].
  - split; 1: by rewrite fun_ext => x; rewrite mem_empty.
    rewrite size_map szts /=; split => [i j u v * | m]; 2: by rewrite mem_empty. 
    by rewrite (nth_map witness witness) /= 2:nthts; 1: admit.
  split => [| rs' skfeles']; 1: by rewrite mkseq0 /=; smt(ge1_k).
  split => [/# | /lezNgt gek_szrsp eqszrsskfep _ lek_szrsp ninqs_sig1].
  pose cmidx := mco _ _; pose fit := List.find _ _.
  rewrite negb_and negb_forall /= => -[| /mem_zip_snd /=]; 2: by rewrite ninqs_sig1.
  move=> -[idxs]; rewrite negb_imply => -[idxsing idxsninlidxs].
  have hasnin : has (fun (idxs : int * int * int) => ! (idxs \in lidxs)) (g (cmidx.`1, cmidx.`2)).
  - by rewrite hasP; exists idxs.
  have rng_fit : 0 <= fit < k.
  - by rewrite find_ge0 /= (: k = size (g (cmidx.`1, cmidx.`2))) 1:/g 1:/= 1:size_mkseq 2:-has_find 2:hasnin; smt(ge1_k).
  move/nth_find: (hasnin) => /= /(_ witness) /= nthgnin.
  rewrite (: val cmidx.`2 = (nth witness (g (cmidx.`1, cmidx.`2)) fit).`1) 1:/cmidx 1:/g /= 1:nth_mkseq 1:rng_fit 1://.
  rewrite nth_mkseq 1:/g /= 1:?nth_mkseq 1:// 1:/= 1:/#.
  move=> eqlf; split; 1: by rewrite -lidxsdef.
  rewrite nthts 5:/=; 1..4: admit.
  rewrite nthxs 5:/=; 1..4: admit.
  by rewrite -eqlf; do ? congr => @{1}/g @/fit /=; rewrite nth_mkseq.
rewrite Pr[mu_split EUF_CMA_MFORSTWESNPRF_V.valid_TRHTCR] StdOrder.RealOrder.ler_add.
+ admit.
admit.
qed.

local lemma EqPr_SMDTOpenPRE_FOpenPRE_FPOpenPRE &m :
  Pr[F_OpenPRE.SM_DT_OpenPRE(R_FSMDTOpenPRE_EUFCMA(A), F_OpenPRE.O_SMDTOpenPRE_Default).main() @ &m : res]
  =
  Pr[FP_OpenPRE.SM_DT_OpenPRE(R_FPOpenPRE_FOpenPRE(A), FP_OpenPRE.O_SMDTOpenPRE_Default).main() @ &m : res].
proof.
byequiv => //.
proc.
conseq (: ={glob A} ==> ={nrts, opened, dist, pp, tw, y} /\ x{1} = val x{2}); 1,2: smt().
seq 4 4 : (   ={pp, i} 
           /\ ={os, ts}(F_OpenPRE.O_SMDTOpenPRE_Default, FP_OpenPRE.O_SMDTOpenPRE_Default)
           /\ x{1} = val x{2}).
+ inline{1} 4; inline{2} 4; inline{2} 6.  
  wp 19 21 => /=.
  conseq (:  ={glob A} 
             ==> 
                ={pp, cidx, x'} 
             /\ ={os, ts}(F_OpenPRE.O_SMDTOpenPRE_Default, FP_OpenPRE.O_SMDTOpenPRE_Default)).
  - by move=> &1 &2; smt(DigestBlock.valKd).
  wp => /=.
  call (:    ={glob R_FSMDTOpenPRE_EUFCMA}
          /\ ={os, ts}(F_OpenPRE.O_SMDTOpenPRE_Default, FP_OpenPRE.O_SMDTOpenPRE_Default)
          /\ F_OpenPRE.O_SMDTOpenPRE_Default.xs{1} = map DigestBlock.val FP_OpenPRE.O_SMDTOpenPRE_Default.xs{2}
          /\ size FP_OpenPRE.O_SMDTOpenPRE_Default.xs{2} = d * k * t).
  - proc; inline *.
    wp => /=.
    while (   ={glob R_FSMDTOpenPRE_EUFCMA, sigFORSTW, cm, tidx, kpidx}
           /\ ={os, ts}(F_OpenPRE.O_SMDTOpenPRE_Default, FP_OpenPRE.O_SMDTOpenPRE_Default)
           /\ F_OpenPRE.O_SMDTOpenPRE_Default.xs{1} = map DigestBlock.val FP_OpenPRE.O_SMDTOpenPRE_Default.xs{2}
           /\ 0 <= kpidx{1} < l
           /\ 0 <= tidx{1} < s
           /\ size FP_OpenPRE.O_SMDTOpenPRE_Default.xs{2} = d * k * t).
    * wp; skip => /> &2 ge0_kp ltl_kp ge0_t lts_t eqdkt_szxs ltk_szsig. 
      rewrite (nth_map witness) 2:size_rcons //= eqdkt_szxs.
      split => [|_]; 1: by rewrite ?StdOrder.IntOrder.addr_ge0 4:bs2int_ge0; smt(size_ge0 ge1_l ge1_k ge2_t).
      rewrite dval (: s * l * k * t = (s - 1) * l * k * t + (l - 1) * k * t + (k - 1) * t + t); 1: by ring.
      rewrite StdOrder.IntOrder.ler_lt_add ?StdOrder.IntOrder.ler_add; 1..3: smt(ge1_l ge1_k ge2_t).
      pose ls := rev _; rewrite (: t = 2 ^ size ls) 2:bs2int_le2Xs /t /ls.
      rewrite size_rev size_take 2:size_drop 3:valP 3:lez_maxr; 1,2,3: smt(ge1_a size_ge0). 
      have: a <= k * a - a * size sigFORSTW{2} by smt(ge1_a size_ge0).
      by case => [-> | <-].
    wp; if => //=.
    * wp; rnd; skip => /> &2 _ mnin mk mkin. 
      move: (Index.valP (mco mk m{2}).`2) => [ge0_idx ltd_idx].
      rewrite get_set_sameE oget_some.
      by rewrite modz_ge0 2:divz_ge0 3:ltz_pmod 4:ltz_divLR 5:-dval; 1..4: smt(Top.ge1_l).
    wp; skip => /> &2 _ _.  
    move: (Index.valP (mco (oget R_FSMDTOpenPRE_EUFCMA.mmap{2}.[m{2}]) m{2}).`2) => [ge0_idx ltd_idx].
    by rewrite modz_ge0 2:divz_ge0 3:ltz_pmod 4:ltz_divLR 5:-dval; 1..4: smt(Top.ge1_l).
  conseq />.
  seq 9 11 : (   ={glob R_FSMDTOpenPRE_EUFCMA, pp}
              /\ ={os, ts}(F_OpenPRE.O_SMDTOpenPRE_Default, FP_OpenPRE.O_SMDTOpenPRE_Default)
              /\ F_OpenPRE.O_SMDTOpenPRE_Default.xs{1} = map DigestBlock.val FP_OpenPRE.O_SMDTOpenPRE_Default.xs{2}
              /\ size FP_OpenPRE.O_SMDTOpenPRE_Default.xs{2} = d * k * t).
  - wp => /=.
    seq 2 2 : (#pre /\ ={pp, tws, R_FSMDTOpenPRE_EUFCMA.ad} /\ size tws{1} = d * k * t).
    * inline *.
      wp.
      while (   ={R_FSMDTOpenPRE_EUFCMA.ad, tidx0}
             /\ adl{1} = adl0{2}
             /\ size adl{1} = tidx0{1} * l * k * t
             /\ 0 <= tidx0{1} <= s).
      + wp => /=.
        while (   ={R_FSMDTOpenPRE_EUFCMA.ad, tidx0, kpidx0}
               /\ adl{1} = adl0{2}
               /\ size adl{1} = tidx0{1} * l * k * t 
                                + kpidx0{1} * k * t
               /\ 0 <= kpidx0{1} <= l).  
        - wp => /=.
          while (   ={R_FSMDTOpenPRE_EUFCMA.ad, tidx0, kpidx0, tbidx}
                 /\ adl{1} = adl0{2}
                 /\ size adl{1} = tidx0{1} * l * k * t
                                  + kpidx0{1} * k * t 
                                  + tbidx{1}
                 /\ 0 <= tbidx{1} <= k * t).
          * by wp; skip => />; smt(size_rcons).
          by wp; skip => />; smt(ge1_k ge2_t). 
        by wp; skip => />; smt(Top.ge1_l).
      by wp; rnd; skip => />; smt(ge1_s dval). 
    inline *.
    wp.
    while (   ={tws_init}
           /\ size tws_init{1} = d * k * t
           /\ ys0{1} = ys1{2}
           /\ ={pp, ts}(O_SMDTOpenPRE_Default, FP_OpenPRE.O_SMDTOpenPRE_Default) 
           /\ O_SMDTOpenPRE_Default.xs{1} = map DigestBlock.val FP_OpenPRE.O_SMDTOpenPRE_Default.xs{2}
           /\ size FP_OpenPRE.O_SMDTOpenPRE_Default.xs{2} = size FP_OpenPRE.O_SMDTOpenPRE_Default.ts{2}
           /\ size FP_OpenPRE.O_SMDTOpenPRE_Default.ts{2} <= min (size tws_init{2}) (d * k * t)).
    * wp; rnd DigestBlock.insubd DigestBlock.val.
      wp; skip => /> &2 eqdkt_sztws. 
      rewrite eqdkt_sztws lez_minr //= => eqszs _ ltdkt_szts.
      split => [* |_]; 1: by rewrite valKd.
      split => [x xin | _ x /supp_dmap [x'] [_ eqvins_x]]. 
      + rewrite (in_dmap1E_can _ _ DigestBlock.insubd) 1,3:valKd //. 
        by move=> y _ <-; rewrite valKd.
      by rewrite eqvins_x valKd /= map_rcons; smt(size_rcons).
    by wp; skip => />; smt(dval ge1_s Top.ge1_l ge1_k ge2_t).
  by conseq />; sim.     
by conseq />; sim.
qed.

(*
local clone F.SMDTDSPR as F_DSPR with
    op t_smdtdspr <- d * k * t
  
  proof *.
  realize ge0_tsmdtdspr by smt(ge1_d ge1_k ge2_t).
  
local module (R_FDSPR_FPDSPR (A : FP_DSPR.Adv_SMDTDSPR) : F_DSPR.Adv_SMDTDSPR) (O : F_DSPR.Oracle_SMDTDSPR) = {  
  module O_SMDTDSPR : FP_DSPR.Oracle_SMDTDSPR = {
    include var FP_DSPR.O_SMDTDSPR_Default [-query]
    
    proc query(ad : adrs, x : dgstblock) : dgstblock = {
      var y : dgstblock;
      var adx : adrs * dgstblock;
      
      y <@ O.query(ad, val x);
      
      adx <- (ad, x);
      ts <- rcons ts adx;
      
      return y;  
    }
  }
  proc pick() : unit = {
    A(O_SMDTDSPR).pick();
  }
  
  proc guess(ps : pseed) : int * bool = {
    var i : int;
    var b : bool;
    
    (i, b) <@ A(O_SMDTDSPR).guess(ps);
    
    return (i, b);
  }
}.

local lemma EqPr_SMDTOpenPRE_FOpenPRE_FPOpenPRE &m (B <: FP_DSPR.Adv_SMDTDSPR):
  Pr[FP_DSPR.SM_DT_DSPR(B, FP_DSPR.O_SMDTDSPR_Default).main() @ &m : res]
  <=
  Pr[F_DSPR.SM_DT_DSPR(R_FDSPR_FPDSPR(B), F_DSPR.O_SMDTDSPR_Default).main() @ &m : res].
proof. admit. qed.
*)

(* 
  TODO:
  I cannot prove that the DSPR advantage for f' is equal to the DSPR advantage
  for f due to the fact it is a distinguishing game.
  The main reason I cannot prove an equality is that f' is simply a 
  domain-restricted version of f, meaning that a second preimage for f' always implies
  a second preimage for f, but not the other way around (because 
  the second preimage for f could be outside the domain of f').
  Contrapositively, no second preimage for f always implies no second preimage for
  f', but not the other way around. So, if the given adversary returns makes the right
  judgment, i.e., true if there is a second preimage under f' and false if there isn't, 
  then in the former case the reduction adversary is always right but in the latter case 
  it might be wrong.  
*)
lemma EUFCMA_MFORSTWESNPRF &m :
  Pr[EUF_CMA_MFORSTWESNPRF(A, O_CMA_MFORSTWESNPRF).main() @ &m : res] 
  <= 
  Pr[MCO_ITSR.ITSR(R_ITSR_EUFCMA(A), MCO_ITSR.O_ITSR_Default).main() @ &m : res]
  +
  (* Pr[F_OpenPRE.SM_DT_OpenPRE(R_FSMDTOpenPRE_EUFCMA(A), F_OpenPRE.O_SMDTOpenPRE_Default).main() @ &m : res]*)
  maxr 0%r 
       (Pr[FP_DSPR.SM_DT_DSPR(R_DSPR_OpenPRE(R_FPOpenPRE_FOpenPRE(A)), FP_DSPR.O_SMDTDSPR_Default).main() @ &m : res]
        -
        Pr[FP_DSPR.SM_DT_SPprob(R_DSPR_OpenPRE(R_FPOpenPRE_FOpenPRE(A)), FP_DSPR.O_SMDTDSPR_Default).main() @ &m : res])
  +
  3%r * Pr[FP_TCR.SM_DT_TCR(R_TCR_OpenPRE(R_FPOpenPRE_FOpenPRE(A)), FP_TCR.O_SMDTTCR_Default).main() @ &m : res]
(*  
  +
  Pr[FC_TCR.SM_DT_TCR_C(R_FSMDTTCRC_EUFCMA(A), FC_TCR.O_SMDTTCR_Default, FC.O_THFC_Default).main() @ &m : res]
*)
  + 
  Pr[TRHC_TCR.SM_DT_TCR_C(R_TRHSMDTTCRC_EUFCMA(A), TRHC_TCR.O_SMDTTCR_Default, TRHC.O_THFC_Default).main() @ &m : res]
  +
  Pr[TRCOC_TCR.SM_DT_TCR_C(R_TRCOSMDTTCRC_EUFCMA(A), TRCOC_TCR.O_SMDTTCR_Default, TRCOC.O_THFC_Default).main() @ &m : res].
proof.
move: (EUFCMA_MFORSTWESNPRF_OPRE &m).
rewrite EqPr_SMDTOpenPRE_FOpenPRE_FPOpenPRE.
move: (OpenPRE_From_DSPR_TCR (R_FPOpenPRE_FOpenPRE(A)) _ _ &m); 3: smt().
+ move=> O.
  proc; inline *.
  wp => /=.
  while (true) (s - tidx).
  - move=> z.
    wp => /=.
    while (true) (l - kpidx).
    * move=> z'.
      wp => /=.
      while (true) (k * t - tbidx).
      + move=> z''.
        by wp; skip => /> /#.
      by wp; skip => /> /#.
    by wp; skip => /> /#.
  by wp; skip => /> /#.
move=> O Oll.
proc; inline *.
wp => /=.
call (: true); 1: by apply A_forge_ll.
+ proc; inline *.
  wp => /=.
  while (true) (k - size sigFORSTW).
  - move=> z.
    wp; call Oll; wp; skip => />; smt(size_rcons).
  wp => /=.
  if; [wp; rnd |]; skip => />; 2: smt().
  by move=> *; rewrite dmkey_ll /#.
while (true) (s - size pkFORSs).
- move=> z.
  wp => /=.
  while (true) (l - size pkFORSl).
  * move=> z'.
    wp => /=.
    while (true) (k - size roots).
    + move=> z''.
      by wp; skip => />; smt(size_rcons).
    by wp; skip => />; smt(size_rcons).
  by wp; skip => />; smt(size_rcons).
by wp; skip => /> /#.        
qed.

end section Proof_EUFCMA_M_FORS_TW_ES.
