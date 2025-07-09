module Foo

#lang-pulse
open Pulse
module T = FStar.Tactics.V2

type abc = | A

let tau () : T.Tac unit =
  T.dump "";
  match_rewrite_tac ()

fn foo (r : ref abc) (#zzz : erased abc)
  preserves r |-> zzz
{
  let z = !r;
  match z {
    A -> { () }
  };
}

let x = 32sz

fn foo_exp (r : ref abc) (#zzz : erased abc)
  preserves r |-> id zzz
{
  let z = !r;
  match z {
    norewrite A -> {
      rewrite each z as A by (tau ());
      ()
    }
  };
}
