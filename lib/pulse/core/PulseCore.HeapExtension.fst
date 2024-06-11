module PulseCore.HeapExtension
open PulseCore.HeapSig
open FStar.Ghost
open FStar.PCM
open FStar.FunctionalExtensionality
module H = PulseCore.Heap
module H2 = PulseCore.Heap2
module F = FStar.FunctionalExtensionality
module PA = PulseCore.PCM.Agreement

assume
val core_ghost_ref_as_addr (_:core_ghost_ref) : GTot nat

assume
val select (i:nat) (m:H2.heap u#a) : GTot (option (H.cell u#a))

assume
val select_ghost (i:nat) (m:H2.heap u#a) : GTot (option (H.cell u#a))

noeq
type core (h:heap_sig u#a) : Type u#(a + 2) = {
    small_core : h.sep.core;
    big_core : H2.heap u#(a + 1);
}

noeq
type ext_mem (h:heap_sig u#a) : Type u#(a + 2) = {
    small : h.mem;
    big : H2.heap u#(a + 1);
    ctr : nat;
    ghost_ctr: erased nat;
}

(* A lens between mem and core *)
let get_core (#h:heap_sig u#h) (m:ext_mem h) : core h = {
    small_core = h.sep.lens_core.get m.small;
    big_core = m.big;
}

let put_core (#h:heap_sig u#h) (c:core h) (m:ext_mem h) : ext_mem h = {
    small = h.sep.lens_core.put c.small_core m.small;
    big = c.big_core;
    ctr = m.ctr;
    ghost_ctr = m.ghost_ctr;
}

let get_put (#h:heap_sig u#h) (m:ext_mem h)
: Lemma (put_core (get_core m) m == m)
= h.sep.lens_core.get_put m.small

let put_get (#h:heap_sig u#h) (c:core h) (m:ext_mem h)
: Lemma (get_core (put_core c m) == c)
= h.sep.lens_core.put_get c.small_core m.small

let put_put (#h:heap_sig u#h) (c1 c2:core h) (m:ext_mem h)
: Lemma (put_core c2 (put_core c1 m) == put_core c2 m)
= h.sep.lens_core.put_put c1.small_core c2.small_core m.small

let lens_core (h:heap_sig u#a) : lens (ext_mem h) (core h) = {
    get = get_core #h;
    put = put_core #h;
    get_put = get_put #h;
    put_get = put_get #h;
    put_put = put_put #h;
}

let empty (#h:heap_sig u#a) : core h = {
    small_core = h.sep.empty;
    big_core = H2.empty_heap;
}

let disjoint (#h:heap_sig u#a) (m1 m2:core h)
: prop
= h.sep.disjoint m1.small_core m2.small_core /\
  H2.disjoint m1.big_core m2.big_core

let join (#h:heap_sig u#a) (m1:core h) (m2:core h { disjoint m1 m2 })
: core h
= {
    small_core = h.sep.join m1.small_core m2.small_core;
    big_core = H2.join m1.big_core m2.big_core;
  }

let disjoint_sym (#h:heap_sig u#a) (m1 m2:core h)
: Lemma (disjoint m1 m2 <==> disjoint m2 m1)
        [SMTPat (disjoint m1 m2)]
= h.sep.disjoint_sym m1.small_core m2.small_core

let join_commutative (#h:heap_sig u#a) (m1:core h) (m2:core h { disjoint m1 m2 })
: Lemma (join m1 m2 == join m2 m1)
        [SMTPat (join m1 m2)]
= h.sep.join_commutative m1.small_core m2.small_core;
  H2.join_commutative m1.big_core m2.big_core

let disjoint_join (#h:heap_sig u#a) (m0 m1 m2:core h)
: Lemma (
      disjoint m1 m2 /\
      disjoint m0 (join m1 m2) ==>
        disjoint m0 m1 /\
        disjoint m0 m2 /\
        disjoint (join m0 m1) m2 /\
        disjoint (join m0 m2) m1)
= h.sep.disjoint_join m0.small_core m1.small_core m2.small_core;
  H2.disjoint_join m0.big_core m1.big_core m2.big_core

let join_associative (#h:heap_sig u#a) 
        (m0:core h)
        (m1:core h)
        (m2:core h { disjoint m1 m2 /\ disjoint m0 (join m1 m2) })
: Lemma (disjoint m0 m1 /\
         disjoint (join m0 m1) m2 /\
         join m0 (join m1 m2) == join (join m0 m1) m2)
= h.sep.join_associative m0.small_core m1.small_core m2.small_core;
  H2.join_associative m0.big_core m1.big_core m2.big_core

let join_associative2 (#h:heap_sig u#a) (m0 m1 m2:core h)
  : Lemma
    (requires
      disjoint m0 m1 /\
      disjoint (join m0 m1) m2)
    (ensures
      disjoint m1 m2 /\
      disjoint m0 (join m1 m2) /\
      join m0 (join m1 m2) == join (join m0 m1) m2)
    [SMTPat (join (join m0 m1) m2)]
  = disjoint_join m2 m0 m1;
    join_commutative m2 m1;
    join_associative m0 m1 m2

let join_empty (#h:heap_sig u#a) (m:core h)
: Lemma (disjoint m (empty #h) /\ join m (empty #h) == m)
        [SMTPatOr [
          [SMTPat (disjoint m (empty#h))];
          [SMTPat (join m (empty #h))]]]
= h.sep.join_empty m.small_core;
  H2.join_empty m.big_core

let ext_sep (h:heap_sig u#a)
: separable (ext_mem h)
= {
    core = core h;
    lens_core = lens_core h;
    empty = empty #h;
    disjoint = disjoint #h;
    join = join #h;
    disjoint_sym = disjoint_sym #h;
    join_commutative = join_commutative #h;
    disjoint_join = disjoint_join #h;
    join_associative = join_associative #h;
    join_empty = join_empty #h;  
  }

let full_mem_pred (h:heap_sig u#a) (m:ext_mem h) : prop =
    h.full_mem_pred m.small /\
    H2.full_heap_pred m.big

let is_ghost_action (h:heap_sig u#a) (m0 m1:ext_mem h) : prop =
    h.is_ghost_action m0.small m1.small /\
    H2.concrete m0.big == H2.concrete m1.big /\
    m0.ctr == m1.ctr

let ext_affine_mem_prop (#m:Type u#a) (sep:separable m)
: Type u#(max 1 a)
= p:(sep.core ^-> prop){ is_affine_mem_prop sep p }

let ext_slprop (h:heap_sig u#a) : Type u#(a + 2) = ext_affine_mem_prop (ext_sep h)
let is_restricted_any (#a #b:Type) (f:a ^-> b) : Lemma (F.is_restricted a f) = ()
let slprop_is_restricted (#h:heap_sig u#a) (p:ext_slprop h) 
: Lemma (is_restricted (ext_sep h).core p)
= is_restricted_any p
let interp (#h:heap_sig u#a) (p:ext_slprop h) : affine_mem_prop (ext_sep h) = p
let as_slprop (#h:heap_sig u#a) (p:affine_mem_prop (ext_sep h)) : ext_slprop h = F.on _ p
let equiv (#h:heap_sig u#a) (p1 p2:ext_slprop h) : prop = forall c. interp p1 c <==> interp p2 c
let slprop_extensionality (h:heap_sig u#a) (p1 p2:ext_slprop h)
: Lemma ((forall c. (interp p1 c <==> interp p2 c)) ==> p1 == p2)
        [SMTPat (equiv p1 p2)]
= introduce (forall (c:(ext_sep h).core). (interp p1 c <==> interp p2 c)) ==> p1 == p2
  with _ . (
    FStar.PredicateExtensionality.predicateExtensionality (ext_sep h).core p1 p2;
    slprop_is_restricted p1;
    slprop_is_restricted p2
  )

let non_info_slprop (h:heap_sig u#a) : non_info (ext_slprop h) = fun x -> reveal x
let bprop (h:heap_sig u#a)  : Type u#(a + 1) = h.slprop

let up_p (#h:heap_sig u#a) (p:h.slprop)
: core h -> prop 
= fun c -> h.interp p c.small_core
let up_p_affine (#h:heap_sig u#a) (p:h.slprop)
: Lemma (is_affine_mem_prop (ext_sep h) (up_p #h p))
= ()
let up (#h:heap_sig u#a) (b:h.slprop) : ext_slprop h = as_slprop #h (up_p b)

let down_p (#h:heap_sig u#a) (p:ext_slprop h)
: h.sep.core -> prop
= fun h -> p { small_core = h; big_core = H2.empty_heap }

let down_p_affine (#h:heap_sig u#a) (p:ext_slprop h)
: Lemma (is_affine_mem_prop h.sep (down_p #h p))
= introduce 
    forall (h1 h2:h.sep.core).
      down_p p h1 /\ h.sep.disjoint h1 h2 ==> down_p p (h.sep.join h1 h2)
  with introduce _ ==> _
  with _ . (
    assert (down_p p h1);
    let h1_ = { small_core = h1; big_core = H2.empty_heap } in
    assert (p h1_);
    let h2_ = { small_core = h2; big_core = H2.empty_heap } in
    H2.join_empty H2.empty_heap;
    assert (disjoint #h h1_ h2_);
    assert ((ext_sep h).disjoint h1_ h2_);
    assert (p (join #h h1_ h2_));
    ()
  )
let down (#h:heap_sig u#a) (p:ext_slprop h) 
: h.slprop
= down_p_affine #h p;
  h.as_slprop (down_p p)

let up_down (#h:heap_sig u#a) (p:h.slprop)
: Lemma (down (up p) == p)
        [SMTPat (down (up p))]
= down_p_affine (up p);
  up_p_affine p;
  introduce forall hh.
    h.interp (down (up p)) hh <==> h.interp p hh
  with  (
    calc (<==>) {
      h.interp (down (up p)) hh;
    (<==>) { h.interp_as (down_p (up p)) }
      down_p (up p) hh;
    (<==>) {}
      down_p (F.on _ (up_p p)) hh;
    (<==>) { h.interp_as (down_p (F.on _ (up_p p))) }
      h.interp p hh;
    };
    ()
  );
  h.slprop_extensionality (down (up p)) p

let non_info_bprop (h:heap_sig u#a) : non_info (bprop h) = h.non_info_slprop
let pure (#h:heap_sig u#a) (p:prop) : ext_slprop h = up (h.pure p)
let emp (#h:heap_sig u#a) : ext_slprop h = up h.emp
let star (#h:heap_sig u#a) (p1 p2:ext_slprop h) 
: ext_slprop h
= as_slprop (fun (c:(ext_sep h).core) ->
    exists (c1 c2 : core h).
      c1 `(ext_sep h).disjoint` c2 /\
      c == (ext_sep h).join c1 c2 /\
      p1 c1 /\
      p2 c2)
let pure_interp (#h:heap_sig u#a) (p:prop) (c:core h) 
: Lemma (interp (pure p) c == p)
= h.pure_interp p c.small_core
let pure_true_emp (#h:heap_sig u#a) (_:unit)
: Lemma (pure #h True == emp #h)
= h.pure_true_emp ()
let intro_emp (#h:heap_sig u#a) (c:core h)
: Lemma (interp (emp #h) c)
= h.intro_emp c.small_core
let emp_unit (#h:heap_sig u#a) (p:ext_slprop h)
: Lemma (p == p `star` emp)
= introduce forall c. 
    (interp p c <==> interp (p `star` emp) c)
  with (
    assert (c == (ext_sep h).join c (empty #h));
    h.intro_emp (empty #h).small_core    
  ); 
  slprop_extensionality h p (p `star` emp)
  
let star_commutative (#h:heap_sig u#a) (p1 p2:ext_slprop h)
: Lemma (p1 `star` p2 == p2 `star` p1)
= assert (equiv (p1 `star` p2) (p2 `star` p1))

#push-options "--z3rlimit_factor 4"
let star_associative (#h:heap_sig u#a) (p1 p2 p3:ext_slprop h)
: Lemma (p1 `star` (p2 `star` p3) == (p1 `star` p2) `star` p3)
= assert (equiv (p1 `star` (p2 `star` p3)) ((p1 `star` p2) `star` p3))
#pop-options

let h2_of_slprop (p:H2.slprop u#a) : H2.a_heap_prop u#a =
  H2.interp_depends_only_on p;
  fun h -> H2.interp p h

let lift (h:heap_sig u#a) (p:H2.slprop u#(a + 1))
: ext_slprop h
= as_slprop (fun c -> h2_of_slprop p c.big_core)

let pts_to (h:heap_sig u#a) (#a:Type u#(a + 1)) (#p:pcm a) (r:ref a p) (x:a)
: ext_slprop h
= lift h (H2.pts_to #a #p r x)

let ghost_pts_to (h:heap_sig u#a) (#a:Type u#(a + 1)) (#p:pcm a) (r:ghost_ref a p) (x:a)
: ext_slprop h
= lift h (H2.ghost_pts_to #a #p r x)

let ext_iname (h:heap_sig u#a) : eqtype = either h.iname nat
let ext_iref (h:heap_sig u#a) : Type0 = erased (either h.iref (ghost_ref _ (PA.pcm_agreement #h.slprop)))
let iref_erasable (h:heap_sig u#a) : non_info (ext_iref h) = fun x -> reveal x
let iname_of (h:heap_sig u#a) (r:ext_iref h) : GTot (ext_iname h) =
  match r with
  | Inl i -> Inl (h.iname_of i)
  | Inr r -> Inr (core_ghost_ref_as_addr r)
let is_boxable (#h:heap_sig u#a) (p:ext_slprop h) = up (down p) == p
let inv (h:heap_sig u#a) (i:ext_iref h) (p:ext_slprop h)
: ext_slprop h
= match i with
  | Inl i -> up (h.inv i (down p))
  | Inr r -> ghost_pts_to h r (Some (down p)) `star` pure (is_boxable p)

let iname_ok (h:heap_sig u#a) (i:ext_iname h) (m:ext_mem h) : prop =
  match i with
  | Inl i -> h.iname_ok i m.small
  | Inr i -> Some? (select_ghost i m.big)

let down_inames (#h:heap_sig u#h) (e:eset (ext_iname h))
: inames h
= let e = Ghost.reveal e in
  FStar.Set.intension (fun i -> Set.mem (Inl i) e)

let sl_pure_imp (#h:heap_sig u#h) (p:prop) (q: squash p -> ext_slprop h) : ext_slprop h =
  as_slprop (fun m -> p ==> interp (q ()) m)

let cell_pred_pre (h:heap_sig u#h) (c:H.cell) =
  let H.Ref a pcm _ = c in
  a == PA.agreement h.slprop /\
  pcm == PA.pcm_agreement #h.slprop

let cell_pred_post (h:heap_sig u#h) (c:H.cell) (_:squash (cell_pred_pre h c)) =
  let H.Ref _ _ v = c in
  let v : PA.agreement h.slprop = v in
  match v with
  | None -> emp
  | Some p -> up p

let invariant_of_one_cell
      (#h:heap_sig u#a)
      (addr:nat)
      (e:eset (ext_iname h))
      (m:H2.heap u#(a + 1))
: ext_slprop h
= if Inr addr `Set.mem` e then emp
  else match select_ghost addr m with
       | Some c -> 
         sl_pure_imp
          (cell_pred_pre h c)
          (cell_pred_post h c)
       | _ -> emp

let rec istore_invariant
         (#h:heap_sig u#a)
         (from:nat)
         (e:eset (ext_iname h))
         (l:H2.heap u#(a + 1))
: ext_slprop h
= invariant_of_one_cell from e l `star` 
  (if from = 0 then emp else istore_invariant (from - 1) e l)

let mem_invariant (#h:heap_sig u#a) (e:eset (ext_iname h)) (m:ext_mem h)
: ext_slprop h
= up (h.mem_invariant (down_inames e) m.small) `star`
  istore_invariant #h m.ctr e m.big

let extend (h:heap_sig u#a) = {
    mem = ext_mem h;
    sep = ext_sep h;
    slprop = ext_slprop h;
    slprop_extensionality = slprop_extensionality h;
    as_slprop = as_slprop #h;
    interp = interp #h;
    interp_as = (fun p -> ());
    full_mem_pred = full_mem_pred h;
    is_ghost_action = is_ghost_action h;
    non_info_slprop = non_info_slprop h;
    bprop = bprop h;
    up = up #h;
    down = down #h;
    up_down = up_down #h;
    non_info_bprop = non_info_bprop h;
    emp = emp;
    pure = pure;
    star = star;
    pure_interp = pure_interp;
    pure_true_emp = pure_true_emp #h;
    emp_unit = emp_unit;
    intro_emp = intro_emp;
    star_commutative = star_commutative;
    star_associative = star_associative;
    star_equiv = (fun p q m -> ());
    pts_to = pts_to h;
    ghost_pts_to = ghost_pts_to h;
    iname = ext_iname h;
    iref = ext_iref h;
    iref_erasable = iref_erasable h;
    iname_of = iname_of h;
    inv = inv h;
    iname_ok = iname_ok h;
    mem_invariant = mem_invariant;
}

let lift_iref (#h:heap_sig u#a) (i:h.iref)
: ext_iref h
= Inl i

let lift_iname (#h:heap_sig u#a) (i:h.iname)
: ext_iname h
= Inl i

let lift_inames (#h:heap_sig u#a) (is:inames h)
: inames (extend h) 
= let is = Ghost.reveal is in
  FStar.Set.intension
    (function
      | Inl i -> i `Set.mem` is
      | _ -> false)

let down_frame
      (#h:heap_sig u#a)
      (p:h.slprop)
      (frame:ext_slprop h)
      (m:ext_mem h { interpret #(extend h) (up p `star` frame) m })
: frame':h.slprop { interpret #h (p `h.star` frame') m.small } &
  (q:h.slprop -> m':h.mem -> 
    Lemma (requires interpret #h (q `h.star` frame') m')
          (ensures interpret #(extend h) (up q `star` frame) ({m with small = m'})))
= admit() 

let down_inames_ok (#h:heap_sig u#a) (ex:inames h) (m:ext_mem h)
: Lemma 
  (ensures inames_ok (lift_inames ex) m <==> inames_ok ex m.small) 
= admit()

let up_star (#h:heap_sig u#a) (p q:h.slprop)
: Lemma (up (p `h.star` q) == (up p `star` up q))
        [SMTPat (up (p `h.star` q))]
= admit()

let up_down_inames (#h:heap_sig u#a) (i:inames h)
: Lemma (down_inames (lift_inames i) == i)
= admit()

let pqrs_pr_qs (h:heap_sig u#a) (p q r s:h.slprop)
: Lemma (
    p `h.star` q `h.star` (r `h.star` s) == (p `h.star` r) `h.star` (q `h.star` s)
)
= admit()

let pqr_prq (h:heap_sig u#a) (p q r:h.slprop)
: Lemma ((p `h.star` q) `h.star` r == p `h.star` r `h.star` q)
= admit()
module T = FStar.Tactics.V2
#push-options "--fuel 0 --ifuel 0 --z3rlimit_factor 4"
let lift_action
    (#h:heap_sig u#h)
    (#a:Type u#a)
    (#mg:bool)
    (#ex:inames h)
    (#pre:h.slprop)
    (#post:a -> h.slprop)
    (action:_action_except h a mg ex pre post)
: _action_except (extend h)
    a mg (lift_inames ex) 
    ((extend h).up pre)
    (fun x -> (extend h).up (post x))
= fun (frame:ext_slprop h) 
      (m0:ext_mem h {
        (extend h).full_mem_pred m0 /\
        inames_ok (lift_inames ex) m0 /\
        interpret #(extend h) (up pre `star` frame `star` mem_invariant (lift_inames ex) m0) m0
       }) ->
        down_inames_ok #h ex m0;
        up_down_inames ex;
        calc (==) {
          up pre `star` frame `star` mem_invariant (lift_inames ex) m0;
        (==) {} 
          up pre `star` frame `star` (up (h.mem_invariant (down_inames (lift_inames ex)) m0.small) `star`
                                      istore_invariant #h m0.ctr (lift_inames ex) m0.big);
        (==) { _ by (T.mapply (quote (pqrs_pr_qs (extend h)))) }
          (up pre `star` up (h.mem_invariant (down_inames (lift_inames ex)) m0.small)) `star` (
           frame `star` istore_invariant #h m0.ctr (lift_inames ex) m0.big
          );
        (==) { () }
          (up (pre `h.star` h.mem_invariant (down_inames (lift_inames ex)) m0.small)) `star` (
           frame `star` istore_invariant #h m0.ctr (lift_inames ex) m0.big
          );
        (==) { }
          (up (pre `h.star` h.mem_invariant ex m0.small)) `star` (
           frame `star` istore_invariant #h m0.ctr (lift_inames ex) m0.big
          );
        };
        let (| frame', restore |) =
          down_frame
            (pre `h.star` h.mem_invariant ex m0.small)
            (frame `star` istore_invariant #h m0.ctr (lift_inames ex) m0.big)
            m0
        in
        calc (==) {
          (pre `h.star` h.mem_invariant ex m0.small) `h.star` frame';
        (==) { _ by (T.mapply (quote (pqr_prq h))) }
          pre `h.star` frame' `h.star` h.mem_invariant ex m0.small;
        };
        let (x, m1') = action frame' m0.small in
        let m1 = { m0 with small = m1' } in
        calc (==) {
          (post x `h.star` frame' `h.star` h.mem_invariant ex m1');
        (==) { _ by (T.mapply (quote (pqr_prq h))) }
          (post x `h.star` h.mem_invariant ex m1') `h.star` frame';
        };
        let _ = restore (post x `h.star` h.mem_invariant ex m1') m1' in
        assert (
          interpret #(extend h)
            (up (post x `h.star` h.mem_invariant ex m1') `star`
            (frame `star` istore_invariant #h m0.ctr (lift_inames ex) m0.big))
          m1
        );
        calc (==) {
          (up (post x `h.star` h.mem_invariant ex m1') `star`
            (frame `star` istore_invariant #h m0.ctr (lift_inames ex) m0.big));
        (==) {}
          (up (post x) `star` up (h.mem_invariant ex m1')) `star`
            (frame `star` istore_invariant #h m0.ctr (lift_inames ex) m0.big);
        (==) { _ by (T.mapply (quote (pqrs_pr_qs (extend h)))) }
          up (post x) `star` frame `star`
            (up (h.mem_invariant ex m1') `star` 
             istore_invariant #h m0.ctr (lift_inames ex) m0.big);
        (==) {}
          up (post x) `star` frame `star`
            (up (h.mem_invariant (down_inames (lift_inames ex)) m1') `star` 
             istore_invariant #h m0.ctr (lift_inames ex) m0.big);
        (==) { () }
          up (post x) `star` frame `star` (mem_invariant (lift_inames ex) m1);
        };
        down_inames_ok #h ex m1;
        (x, m1)

